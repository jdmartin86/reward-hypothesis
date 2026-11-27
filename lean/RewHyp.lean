import Mathlib
universe u

set_option linter.unusedFintypeInType false

-- Utility definitions
abbrev ClosedInterval01 : Type  := {x : ℝ // 0 ≤ x ∧ x ≤ 1}
abbrev OpenInterval01 : Type  := {x : ℝ // 0 < x ∧ x < 1}
def OpenInterval01.toClosed (α : OpenInterval01) : ClosedInterval01 :=
  ⟨α.1, α.2.1.le, α.2.2.le⟩

-- Preference relation over lotteries
class Preference (L : Type u) where
  pref : L → L → Prop
notation:50 p " ≽ " q => Preference.pref p q

def strict_pref {L : Type u} [Preference L] (p q : L) : Prop :=
  (p ≽ q) ∧ ¬ (q ≽ p)
notation:50 p " ≻ " q => strict_pref p q

def indeff_pref {L : Type u} [Preference L] (p q : L) : Prop :=
  (p ≽ q) ∧ (q ≽ p)
notation:50 p " ~ " q => indeff_pref p q

-- Histories of observations and actions
variable (O A : Type) [Fintype O] [Fintype A]
abbrev Transition : Type := O × A
abbrev History : Type := List (Transition O A)
abbrev ε : History O A := []
abbrev HistoryDistribution : Type := PMF (History O A)
noncomputable abbrev diracHistory (h : History O A) : HistoryDistribution O A :=
  PMF.pure h

-- Mixture (convex combination) of two probability mass functions: αP + (1-α)Q
noncomputable def mix (P Q : PMF (History O A)) (α : ClosedInterval01) :
    HistoryDistribution O A :=
  ⟨fun h ↦ ENNReal.ofReal α.1 * P h + ENNReal.ofReal (1 - α.1) * Q h,
    ENNReal.summable.hasSum_iff.2 (by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
        P.tsum_coe, Q.tsum_coe, mul_one, mul_one,
        ← ENNReal.ofReal_add α.2.1 (sub_nonneg.2 α.2.2), add_sub_cancel]
      exact ENNReal.ofReal_one)⟩

noncomputable def HistoryDistribution.cons (t : Transition O A)
    (P : HistoryDistribution O A) : HistoryDistribution O A :=
  PMF.map (fun h ↦ t :: h) P

-- Type helper
theorem cons_apply_cons (t : Transition O A) (P : HistoryDistribution O A) (h : History O A) :
    HistoryDistribution.cons O A t P (t :: h) = P h := by
  unfold HistoryDistribution.cons
  rw [PMF.map_apply, tsum_eq_single h]
  · simp
  · intro b hb
    simp only [List.cons.injEq, true_and, ite_eq_right_iff]
    intro e; exact absurd e.symm hb

theorem cons_apply_not_mem (t : Transition O A) (P : HistoryDistribution O A) (h' : History O A)
    (hh : h' ∉ Set.range (fun h : History O A ↦ t :: h)) :
    HistoryDistribution.cons O A t P h' = 0 := by
  unfold HistoryDistribution.cons
  rw [PMF.map_apply]
  refine ENNReal.tsum_eq_zero.2 fun a ↦ ?_
  simp only [ite_eq_right_iff]
  intro e; exact absurd ⟨a, e.symm⟩ hh

-- Type helper: prepending `t` to the Dirac lottery on `h` gives the Dirac lottery on `t :: h`.
theorem cons_dirac (t : Transition O A) (h : History O A) :
    HistoryDistribution.cons O A t (diracHistory O A h) = diracHistory O A (t :: h) := by
  unfold HistoryDistribution.cons diracHistory
  exact PMF.pure_map _ _

-- Lifts the additive rule u(t·h) = r(t) + γ(t)·u(h) from single histories to any
-- distribution P by reindexing the expected-utility sum along the injective map `t :: ·`.
theorem u_cons (u : HistoryDistribution O A → ℝ) (r : Transition O A → ℝ) (g : Transition O A → ℝ)
    (h_sub : ∀ (t : Transition O A) (h : History O A),
        u (HistoryDistribution.cons O A t (diracHistory O A h))
          = r t + g t * u (diracHistory O A h))
    (hev : ∀ P : HistoryDistribution O A,
      Summable (fun h : History O A ↦ (P h).toReal * u (diracHistory O A h)) ∧
      u P = ∑' h : History O A, (P h).toReal * u (diracHistory O A h))
    (t : Transition O A) (P : HistoryDistribution O A) :
    u (HistoryDistribution.cons O A t P) = r t + g t * u P := by
  let f : History O A → ℝ := fun h' ↦
    (HistoryDistribution.cons O A t P h').toReal * u (diracHistory O A h')
  have hreindex : ∑' h' : History O A, f h' = ∑' h : History O A, f (t :: h) := by
    refine ((List.cons_injective (a := t)).tsum_eq (f := f) ?_).symm
    intro h' hh'
    by_contra hn
    exact hh' (by
      simp only [f]
      rw [show HistoryDistribution.cons O A t P h' = 0 from
        cons_apply_not_mem O A t P h' hn, ENNReal.toReal_zero, zero_mul])
  rw [(hev _).2, (hev P).2]
  change ∑' h' : History O A, f h' = _
  rw [hreindex]
  simp only [f, cons_apply_cons]
  simp_rw [← cons_dirac, h_sub, mul_add]
  have hs1 : Summable (fun h : History O A ↦ (P h).toReal) :=
    ENNReal.summable_toReal (by simp [P.tsum_coe])
  have h1 : ∑' h : History O A, (P h).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (PMF.apply_ne_top P), P.tsum_coe, ENNReal.toReal_one]
  have hs2 := (hev P).1.mul_left (g t)
  simp_rw [mul_left_comm _ (g t)]
  rw [Summable.tsum_add (hs1.mul_right _) hs2, tsum_mul_right, h1, one_mul, tsum_mul_left]

-- Rationality Axioms
variable [Preference (HistoryDistribution O A)]

def A1_Completeness : Prop :=
  ∀ P Q : HistoryDistribution O A, (P ≽ Q) ∨ (Q ≽ P)

def A2_Transitivity : Prop :=
  ∀ P Q R : HistoryDistribution O A, (P ≽ Q) ∧ (Q ≽ R) → (P ≽ R)

def A3_Independence : Prop :=
  ∀ (P Q R : HistoryDistribution O A) (α : OpenInterval01),
  ((P ≽ Q) ↔ mix O A P R α.toClosed ≽ mix O A Q R α.toClosed)

def A4_Continuity : Prop :=
  ∀ (P Q R : HistoryDistribution O A),
  (P ≽ Q) ∧ (Q ≽ R) → ∃ α : ClosedInterval01, (mix O A P R α) ~ Q

def vNMAxioms : Prop :=
  A1_Completeness O A ∧
  A2_Transitivity O A ∧
  A3_Independence O A ∧
  A4_Continuity O A

-- Theorem 3.1 (von Neumann Morgenstern Theorem)
theorem vNM_Theorem :
  vNMAxioms O A↔
    ∃ u : HistoryDistribution O A → ℝ,
      u (diracHistory O A (ε O A)) = 0 ∧
      (∀ P Q : HistoryDistribution O A, (P ≽ Q) ↔ u Q ≤ u P) ∧
      (∀ P : HistoryDistribution O A,
        Summable (fun h : History O A ↦ (P h).toReal * u (diracHistory O A h)) ∧
        u P = ∑' h : History O A, (P h).toReal * u (diracHistory O A h)) := by
    sorry

theorem u_mix (u : HistoryDistribution O A → ℝ)
    (hev : ∀ P : HistoryDistribution O A,
      Summable (fun h : History O A ↦ (P h).toReal * u (diracHistory O A h)) ∧
      u P = ∑' h : History O A, (P h).toReal * u (diracHistory O A h))
    (P Q : HistoryDistribution O A) (α : ClosedInterval01) :
    u (mix O A P Q α) = α.val * u P + (1 - α.val) * u Q := by
  have hmix : ∀ h, ((mix O A P Q α) h).toReal = α.val * (P h).toReal + (1 - α.val) * (Q h).toReal := by
    intro h
    change (ENNReal.ofReal α.1 * P h + ENNReal.ofReal (1 - α.1) * Q h).toReal = _
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top P h))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top Q h)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal α.2.1,
      ENNReal.toReal_ofReal (sub_nonneg.2 α.2.2)]
  rw [(hev _).2, (hev P).2, (hev Q).2]
  simp_rw [hmix, add_mul, mul_assoc]
  rw [Summable.tsum_add ((hev P).1.mul_left _) ((hev Q).1.mul_left _), tsum_mul_left, tsum_mul_left]

-- The weight 1 / (1 + γ), for any γ ∈ [0,1].
noncomputable def ClosedInterval01.discount (γ : ClosedInterval01) : ClosedInterval01 :=
  ⟨1 / (1 + γ.1),
    div_nonneg zero_le_one (by linarith [γ.2.1]),
    (div_le_one (by linarith [γ.2.1])).2 (by linarith [γ.2.1])⟩

def A5_TemporalγIndifference : Prop :=
  ∃ γ : Transition O A → ClosedInterval01,
    ∀ (P Q : HistoryDistribution O A) (t : Transition O A),
      let g := ClosedInterval01.discount (γ t)
      mix O A (HistoryDistribution.cons O A t P) Q g ~
      mix O A (HistoryDistribution.cons O A t Q) P g

def SatisfiesAxioms : Prop :=
  vNMAxioms O A ∧ A5_TemporalγIndifference O A

-- 5. Theorem 4.1 (Markov Reward Theorem)
theorem Markov_Reward_Theorem :
    SatisfiesAxioms O A ↔
    ∃ (u : HistoryDistribution O A → ℝ)
      (r : Transition O A → ℝ)
      (γ : Transition O A → ClosedInterval01),
      -- Condition 1. u of the empty history ε is 0
      u (diracHistory O A (ε O A)) = 0 ∧
      -- Condition 2. additive substructure u(t · h) = r(t) + γ(t) u(h)
      (∀ (t : Transition O A) (h : History O A),
        u (HistoryDistribution.cons O A t (diracHistory O A h))
          = r t + (γ t).val * u (diracHistory O A h)) ∧
      -- Condition 3. u represents the preference
      (∀ P Q : HistoryDistribution O A, (P ≽ Q) ↔ u Q ≤ u P) ∧
      -- Condition 4. u is linear over mixtures: u(∑ pᵢ hᵢ) = ∑ pᵢ u(hᵢ)
      (∀ P : HistoryDistribution O A,
        Summable (fun h : History O A ↦ (P h).toReal * u (diracHistory O A h)) ∧
        u P = ∑' h : History O A, (P h).toReal * u (diracHistory O A h)) := by
        apply Iff.intro
        · intro h -- (→) Forward direction
          -- Unpack vNM to construct r = u
          have vnm : vNMAxioms O A := h.1
          have h_exists := (vNM_Theorem O A).mp vnm
          rcases h_exists with ⟨u, h_ε, hu_pref, hu_lin⟩
          let r := fun t ↦ u (diracHistory O A [t])

          -- Unpack Temporal γ-Indifference axiom for existence of γ
          rcases h with ⟨_, temp_γ_indiff⟩
          rcases temp_γ_indiff with ⟨γ, h_gamma_prop⟩
          use u, r, γ
          refine ⟨h_ε, ?_, hu_pref, hu_lin⟩
          · intro t h_hist
            -- 1. Instantiate A5 for P = h_hist and Q = ε
            let δ_ε := (diracHistory O A (ε O A))
            let δ_h := (diracHistory O A h_hist)
            have h_inst := h_gamma_prop δ_h δ_ε t

            -- 2. Turn the mixture indifference into a utility equality using hu_pref
            let δ_th := (HistoryDistribution.cons O A t δ_h)
            let δ_tε := (HistoryDistribution.cons O A t δ_ε)
            let δ_thε := mix O A δ_th δ_ε (ClosedInterval01.discount (γ t))
            let δ_tεh := mix O A δ_tε δ_h (ClosedInterval01.discount (γ t))
            let u_thε := u δ_thε
            let u_tεh := u δ_tεh
            have h_utils_equal : u_thε = u_tεh := by
              -- Proof by splitting indifference into two hypotheses
              rcases h_inst with ⟨h_pref1, h_pref2⟩
              have eq1 := (hu_pref δ_thε δ_tεh).mp h_pref1
              have eq2 := (hu_pref δ_tεh δ_thε).mp h_pref2
              linarith

            -- Establish the expansions in terms of γ weights
            let δ_th := (HistoryDistribution.cons O A t δ_h)
            let α := ClosedInterval01.discount (γ t)
            have expand_thε : u_thε = α * u δ_th + (1 - α) * u δ_ε := by
              exact u_mix O A u hu_lin δ_th δ_ε α
            have expand_tεh : u_tεh = α * u δ_tε + (1 - α) * u δ_h := by
              exact u_mix O A u hu_lin δ_tε δ_h α

            -- Clear terms involving u δ_ε = 0
            have reduced_thε : u_thε = α * u δ_th := by
              rw [expand_thε, h_ε, mul_zero, add_zero]
            have r_tε : u δ_tε = r t := by
              exact congrArg u (cons_dirac O A t (ε O A))
            have reduced_tεh : u_tεh = α * r t + (1 - α) * u δ_h := by
              rw [expand_tεh, r_tε]

            -- Eliminate denominators
            have h_combined : α * u δ_th = α * (r t) + (1 - α) * u δ_h := by
              linarith [h_utils_equal, reduced_thε, reduced_tεh]
            have hpos : 0 < 1 + (γ t).1 := by linarith [(γ t).2.1]
            have hα : (α : ℝ) = 1 / (1 + (γ t).1) := rfl
            rw [hα] at h_combined
            field_simp at h_combined
            have final_eq : u δ_th = r t + γ t * u δ_h := by linarith
            exact final_eq
        · intro h -- (←) Reverse direction
          rcases h with ⟨u, r, γ, h_ε, h_δsub, h_pref, h_lin⟩

          -- Axioms 1-4 follow from vNM
          have h_vnm : vNMAxioms O A := (vNM_Theorem O A).mpr ⟨u, h_ε, h_pref, h_lin⟩
          apply And.intro
          · exact h_vnm

          -- Establish additive substructure for any distribution μ.
          unfold A5_TemporalγIndifference
          refine ⟨γ, ?_⟩
          intro P Q t g
          have h_μsub := u_cons O A u r (fun t => (γ t).1) h_δsub h_lin

          -- Establish an equivalence with generic distributions.
          have h_umix :
            let μ_tP := (HistoryDistribution.cons O A t P)
            let μ_tQ := (HistoryDistribution.cons O A t Q)
            (u μ_tP + (γ t).1 * u Q) * (1 / (1 + (γ t).1)) =
            (u μ_tQ + (γ t).1 * u P) * (1 / (1 + (γ t).1)) := by
              dsimp only
              rw [h_μsub t P, h_μsub t Q]
              ring

          -- Establish positivity for division.
          have h_pos : 0 < 1 + (γ t).1 := by linarith [(γ t).2.1]

          -- Establish indifference.
          have h_ind :
            let μ_tP := (HistoryDistribution.cons O A t P)
            let μ_tQ := (HistoryDistribution.cons O A t Q)
            u (mix O A μ_tP Q g) = u (mix O A μ_tQ P g) := by
              dsimp
              rw [u_mix O A u h_lin, u_mix O A u h_lin]
              have hg : (g : ℝ) = 1 / (1 + (γ t).1) := rfl
              rw [hg]
              dsimp only at h_umix
              field_simp at h_umix ⊢
              linarith
          exact ⟨(h_pref _ _).2 h_ind.ge, (h_pref _ _).2 h_ind.le⟩
