Farsighted Probabilistic Sampling: A General Strategy for Boosting MaxSAT Local Search Solvers
----
This repository contains the code to the (Max)SAT algorithms improved by FPS, including MaxFPS, BandMaxSAT-FPS, CCEHC-FPS, Dist-FPS, and CCAnr-FPS, proposed in our paper: <br> <br>
[Farsighted Probabilistic Sampling: A General Strategy for Boosting MaxSAT Local Search Solvers](https://arxiv.org/abs/2108.09988#) <br>
Jiongzhi Zheng, Kun He, Jianrong Zhou <br> <br>

Installation
----
The cut-off time for each (W)PMS (resp. SAT) algorithm is set to 300 (resp. 3600) seconds. <br>
The random seed for each algorithm is set to 1 by default. <br>
The parameters of these algorithms are their default settings. <br> <br> <br>


To run MaxFPS, you need to execute the following commands on a Unix/Linux machine: <br> <br>

cd MaxFPS <br>
make <br>
./MaxFPS *.wcnf <br> <br>

The algorithms SATLike3.0, BandMaxSAT, Dist, Dist-FPS, BandMaxSAT-FPS can be run in the same way. <br> <br> <br>


To run CCEHC-FPS or CCEHC, you need to execute the following commands on a Unix/Linux machine: <br> <br>

cd CCEHC-FPS (or cd CCEHC) <br>
make <br>
./CCEHC-FPS (or ./CCEHC) -inst *.wcnf -seed 1 -t 300 -p 0.2 -sp 0.0001 <br> <br> <br>


To run CCAnr-FPS or CCAnr, you need to execute the following commands on a Unix/Linux machine: <br> <br>

cd CCAnr-FPS (or cd CCAnr) <br>
make <br>
./CCAnr-FPS (or ./CCAnr) -inst *.cnf <br> <br> <br>


Contact
----
Questions and suggestions can be sent to jzzheng@hust.edu.cn. <br> <br>

Citation
----
If you find this code useful, please consider citing the original work by authors: <br>
```
@article{zheng2022FPS,
  author    = {Jiongzhi Zheng and
               Jianrong Zhou and
               Kun He},
  title     = {Farsighted Probabilistic Sampling based Local Search for (Weighted)
               Partial MaxSAT},
  journal   = {CoRR},
  volume    = {abs/2108.09988},
  year      = {2021},
  url       = {https://arxiv.org/abs/2108.09988}
}
```
