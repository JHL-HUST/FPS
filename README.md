Farsighted Probabilistic Sampling: A General Strategy for Boosting MaxSAT Local Search Solvers
----
This repository contains the code to the (Max)SAT algorithms improved by FPS, including MaxFPS, BandMaxSAT-FPS, CCEHC-FPS, Dist-FPS, and CCAnr-FPS, proposed in our paper: <br> <br>
[Farsighted Probabilistic Sampling: A General Strategy for Boosting MaxSAT Local Search Solvers](https://arxiv.org/abs/2108.09988#) <br>
Jiongzhi Zheng, Kun He, Jianrong Zhou <br> <br>

Installation
----
The cut-off time for each (W)PMS (resp. SAT) algorithm is set to 300 (resp. 3600) seconds. <br>
The random seed for each algorithm is set to 1 by default. <br>
The parameters of these algorithms are their default settings. <br> <br>

To run MaxFPS, you need to execute the following commands on a Unix/Linux machine: <br>

cd MaxFPS <br>
make <br>
./MaxFPS *.wcnf <br>

The algorithms Dist-FPS and BandMaxSAT-FPS can be run in the same way. <br> <br>

To run CCEHC-FPS, you need to execute the following commands on a Unix/Linux machine: <br>

cd CCEHC-FPS <br>
make <br>
./CCEHC-FPS -inst *.wcnf -seed 1 -t 300 -p 0.2 -sp 0.0001 <br> <br>

To run CCAnr-FPS, you need to execute the following commands on a Unix/Linux machine: <br>

cd CCAnr-FPS <br>
make <br>
./CCAnr-FPS -inst *.cnf <br> <br>

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
