# The Reward Hypothesis

This repository contains code for computing a reward and discount function that respect preconditions for the Reward Hypothesis.

The Reward Hypothesis claims that   
_All that we mean by goals and purposes can be well thought of as maximization of a scalar reward signal._  
This idea is due to Michael Littman and Rich Sutton.

2023 ICML Paper: [Settling the Reward Hypothesis](https://arxiv.org/abs/2212.10420).

#### Build and Run
1. Clone this git repo and enter the directory.
```
git clone git@github.com:jdmartin86/reward-hypothesis.git
cd reward-hypothesis
```

2. Build the Docker image.
```
docker build -t rh .
```

3. Run the Docker image.
```
docker run rh
```

#### Citation
To cite this paper use the following
```
@inproceedings{bowling2023settling,
  title={Settling the reward hypothesis},
  author={Bowling, Michael and Martin, John D and Abel, David and Dabney, Will},
  booktitle={International Conference on Machine Learning},
  pages={3003--3020},
  year={2023},
  organization={PMLR}
}
```
