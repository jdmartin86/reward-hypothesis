"""""
Evaluates algorithms that convert preferences to value functions using rational
representations.
"""
from itertools import product

"""
Utilities
"""
def utility(reward, gamma, hist):
  def helper(ts):
    t, *ts = ts
    if len(ts) == 0:
      return reward[t]
    return reward[t] + gamma[t] * helper(ts)

  ts = hist.split(',')
  return helper(ts)

def minmax(dictionary):
  k, v = next(iter(dictionary.items()))
  best = {'k': k, 'v': v}
  worst = {'k': k, 'v': v}

  for k, v in dictionary.items():
    if v > best['v']:
      best = {'k': k, 'v': v}
    if v < worst['v']:
      worst = {'k': k, 'v': v}
  
  return worst, best

def get_two_step_hists(t_list):
  up_to_two_step = [','.join(ts) for ts in product(t_list, t_list)]
  return [h for h in up_to_two_step if 'e' not in h]

def normalize(util):
  worst, best = minmax(util)
  denom = best['v'] if best['v'] > 0 else abs(worst['v'])
  return {k: v/denom for k, v in util.items()}

"""
Subroutines
"""
def pref_sort(hist_list, true_utils):
  return [k for k, v in sorted(true_utils.items(), key=lambda item: item[1])]

def pref_scale(hist_list, true_utils):
  low = true_utils[hist_list[0]]
  high = true_utils[hist_list[-1]]
  p = {k: (v-high)/(low-high) for k, v in true_utils.items()}
  return p

def assign_utility(sorted_hist_list, p):
  """Lines 4-8 and 12-16"""
  eps_idx = sorted_hist_list.index('e') + 1  # want 1-indexed array
  n = len(sorted_hist_list)

  u = {k: p[k]*(1 - eps_idx) + (1-p[k])*(1-eps_idx/n) for k in sorted_hist_list}
  u['e'] = 0
  return u

def get_gammas(utils):
  """
  Uses two-step transitions of the form't,t' instead of 't, best_t'. 
  Shouldn't change the result.
  """
  t_list = [k for k in utils if len(k.split(',')) == 1 and k != 'e']
  gamma = {k: (utils[f"{k},{k}"] - utils[k]) / utils[k] for k in t_list}
  gamma['e'] = 1
  return gamma

"""
Algorithms
"""
def alg1_strict(reward, gamma, t_list):
  """
  Strict means TxT includes only 2-step histories and epsilon. I
  believe this is faithful to the pseudocode in the paper.
  """
  # set up
  one_utils = {h: utility(reward, gamma, h) for h in t_list}
  hists = get_two_step_hists(t_list) + ['e']
  two_utils = {h: utility(reward, gamma, h) for h in hists}

  # Lines 1-8
  sorted_t = pref_sort(t_list, one_utils)
  p = pref_scale(sorted_t, one_utils)
  util_t = assign_utility(sorted_t, p)

  # Lines 9-16
  sorted_hists = pref_sort(hists, two_utils)
  p = pref_scale(sorted_hists, two_utils)
  util_tt = assign_utility(sorted_hists, p)
  
  # Lines 17-20
  util = dict(util_tt, **util_t)
  r = {k: v for k, v in util.items() if len(k.split(',')) == 1}
  g = get_gammas(util)
  return r, g

def alg1_weak_one(reward, gamma, t_list):
  """
  Weak means TxT includes all histories of UP TO length 2.
  One means the reward fn from Lines 1-8 (numbers in comments) overrides the 
  utility fn calculated in Lines 9-16.
  """
  # Setup
  one_utils = {h: utility(reward, gamma, h) for h in t_list}
  hists = get_two_step_hists(t_list) + t_list
  two_utils = {h: utility(reward, gamma, h) for h in hists}

  # Lines 1-8
  sorted_t = pref_sort(t_list, one_utils)
  p = pref_scale(sorted_t, one_utils)
  util_t = assign_utility(sorted_t, p)

  # Lines 9-16
  sorted_hists = pref_sort(hists, two_utils)
  p = pref_scale(sorted_hists, two_utils)
  util_tt = assign_utility(sorted_hists, p)

  # Lines 17-20
  util = dict(util_tt, **util_t)
  r = {k: v for k, v in util.items() if len(k.split(',')) == 1}
  g = get_gammas(util)

  return r, g

def alg1_weak_two(reward, gamma, t_list):
  """
  Weak means TxT includes all histories of UP TO length 2.
  Two means the reward fn from Lines 1-8 (numbers in comments) is overridden by
  the utility fn calculated in Lines 9-16.
  """
  # Setup
  one_utils = {h: utility(reward, gamma, h) for h in t_list}
  hists = get_two_step_hists(t_list) + t_list
  two_utils = {h: utility(reward, gamma, h) for h in hists}

  # Lines 1-8
  sorted_t = pref_sort(t_list, one_utils)
  p = pref_scale(sorted_t, one_utils)
  util_t = assign_utility(sorted_t, p)

  # Lines 9-16
  sorted_hists = pref_sort(hists, two_utils)
  p = pref_scale(sorted_hists, two_utils)
  util_tt = assign_utility(sorted_hists, p)
  util = dict(util_t, **util_tt)

  # Lines 17-20
  r = {k: v for k, v in util.items() if len(k.split(',')) == 1}
  g = get_gammas(util)

  return r, g

def alg_niko(reward, gamma, t_list):
  """
  This algorithm works in this context. I believe it will work generally. It
  only uses O(T) histories to compute the reward and gamma.
  """
  # get all 1 and 2 step histories (just |T| + 2|T| histories, different from paper)
  twos = [h for h in get_two_step_hists(t_list) if h.split(',')[0] == h.split(',')[1]]
  hists = twos + t_list

  # get preferences
  true_utils = {t: utility(reward, gamma, t) for t in hists}

  # sort, prefscale
  sorted_hists = pref_sort(hists, true_utils)
  p = pref_scale(sorted_hists, true_utils)

  # assign utility (different from paper)
  invp = {k: 1-p[k] for k in sorted_hists}
  util = {k: v - invp['e'] for k, v in invp.items()}

  # output
  r = {k: v for k, v in util.items() if len(k.split(',')) == 1}
  g = get_gammas(util)
  return r, g

"""
Experiments
"""
import random
from functools import partial

def eval(true_r, true_g, alg_r, alg_g, eps=10e-6, verbose=False):
  # define utility functions
  true_util = partial(utility, true_r, true_g)
  alg_util = partial(utility, alg_r, alg_g)
  
  # get histories
  t_list = list(true_r.keys())
  hists = get_two_step_hists(t_list) + t_list

  # make utility dictionaries
  utils_t = {h: true_util(h) for h in hists}
  utils_a = {h: alg_util(h) for h in hists}

  # normalize
  norm_t = normalize(utils_t)
  norm_a = normalize(utils_a)

  # output
  res = {}
  for k, v in norm_t.items():
    res[k] = {'true': v,
              'algo': norm_a[k],
              'close': v - eps < norm_a[k] < v + eps}

  return res


def get_random_value_function(min_t, max_t):
  num_transitions = random.randint(min_t, max_t)

  reward = {f'{i}' : random.uniform(-10, 10) for i in range(1, num_transitions)}
  reward['e'] = 0

  gamma = {f'{i}' : random.random() for i in range(1, num_transitions)}
  gamma['e'] = 1

  return reward, gamma

def main():
  num_trials = 100
  min_t, max_t = 3, 100

  algs = {
        'alg1_strict': alg1_strict, 
        'alg1_weak_one': alg1_weak_one,
        'alg1_weak_two': alg1_weak_two,
        'alg_niko': alg_niko
  }

  res = {k: 0 for k in algs}

  for i in range(num_trials):
    reward, gamma = get_random_value_function(min_t, max_t)
    t_list = list(reward.keys())

    for name, alg in algs.items():
      alg_r, alg_g = alg(reward, gamma, t_list)
      inner_res = eval(reward, gamma, alg_r, alg_g)
      success = all(v['close'] for k, v in inner_res.items())
      if success:
        res[name] += 1
      
      if 'niko' in name and not success:
        for k in inner_res:
          print(f'{k}:')
          for j in inner_res[k]:
            print(f'\t{j}\t=\t{inner_res[k][j]}')
        print('\n\n')
        0/0
  
  for k, v in res.items():
    print(f'{k}: {v}/{num_trials}')

main()