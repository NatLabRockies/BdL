# BdL: Biological Differential Dynamic Logic

**A Formal Analyzer of Dynamical Systems using Deductive Proofs for Biological Computing and its Applications**

[![License: BSD 3-Clause](https://img.shields.io/badge/License-BSD_3--Clause-blue.svg)](LICENSE)

- **NLR Software Record:** SWR 26-101
- **Checked with:** Isabelle2025-2 and the matching release of the [Archive of Formal Proofs](https://www.isa-afp.org/) (AFP)

## About

BdL mechanizes proof rules of differential dynamic logic (dL) in Isabelle/HOL, on top of Fabian Immler's formalization of ordinary differential equations in the AFP (commonly called HOL-ODE). It targets ODE models of dynamical systems, with biological computing as its first application. Invariance, reachability, and convergence properties are proved deductively from local conditions on the derivatives, without solving the ODEs.

The case studies cover induced switching in the Gardner genetic toggle switch, safety of a bioreactor model, and benchmarks on chemical reaction networks (CRNs), gene regulatory networks (GRNs), and a programmable biological circuit.

## Repository contents

| File | Description |
|------|-------------|
| `Real_Analysis_More.thy` | Supporting analysis: vector algebra, manipulation of ODE solutions, scalar and vector-component derivatives, Hill-function calculus, and Lie derivatives |
| `Differential_Dynamic_Logic.thy` | The dL proof rules: differential induction (DI), differential ghost (DG), differential cut (DC), DI boundary, DI convergence rate, Lyapunov reachability, and the DI rectangle box (DI frame rule) |
| `General_Purpose_Examples.thy` | Small examples applying DI and DG |
| `Gardner_Stability_Proof.thy` | Case study: induced switching of the Gardner toggle switch via trapping regions and Lyapunov reachability, with a concrete parameter instantiation |
| `Bioreactor_Safety_Proof.thy` | Case study: forward invariance of a safety region and Z-clearance under operational bounds for a bioreactor model, with a concrete metabolic instantiation |
| `Biological_Computing_Benchmark_Proofs.thy` | Benchmark proofs for CRNs, GRNs, and a programmable biological circuit |
| `ROOT` | Isabelle session specification (session `BdL`) |
| `CONTRIBUTORS`, `CITATION.cff`, `LICENSE` | Authors, citation metadata, and license |

Theory dependencies:

```text
Ordinary_Differential_Equations (AFP)
└── Real_Analysis_More
    └── Differential_Dynamic_Logic
        ├── General_Purpose_Examples
        ├── Gardner_Stability_Proof
        ├── Bioreactor_Safety_Proof
        └── Biological_Computing_Benchmark_Proofs
```

## Requirements

1. **Isabelle2025-2**, from <https://isabelle.in.tum.de/>
2. **The AFP release for Isabelle2025-2**, from <https://www.isa-afp.org/>

BdL uses the AFP entry [Ordinary_Differential_Equations](https://www.isa-afp.org/entries/Ordinary_Differential_Equations.html) (HOL-ODE). Each AFP release is built for exactly one Isabelle release, so the two versions must match.

## Setup

In the commands below, `isabelle` is the `bin/isabelle` executable inside your Isabelle installation.

### 1. Install Isabelle

Download Isabelle2025-2 for your platform and install it as described on the Isabelle website.

### 2. Install the AFP and register it with Isabelle

Download the AFP release for Isabelle2025-2 and unpack it, for example to `/home/myself/afp`. Then register the AFP's `thys` directory as an Isabelle component, as recommended at <https://www.isa-afp.org/help>:

```bash
# Linux / macOS
isabelle components -u /home/myself/afp/thys

# Windows (in a Cygwin terminal), with the AFP unpacked to C:\afp
isabelle components -u /cygdrive/c/afp/thys
```

This is a one-time step. Afterwards every AFP entry, including `Ordinary_Differential_Equations`, is available to Isabelle as a session.

### 3. Get BdL

```bash
git clone https://github.com/NatLabRockies/BdL.git
cd BdL
```

### 4. Check all theories in batch mode

```bash
isabelle build -v -D .
```

The first run also builds the session images BdL depends on (`HOL-Analysis`, `Ordinary_Differential_Equations`, and their prerequisites), which takes a while; later runs reuse them. The check succeeds when the build reports session `BdL` as finished with no errors.

To use the AFP without registering it in step 2, pass its location directly:

```bash
isabelle build -v -d /home/myself/afp/thys -D .
```

### 5. Explore the proofs interactively

```bash
isabelle jedit -d . -R BdL Differential_Dynamic_Logic.thy
```

`-R BdL` starts Isabelle/jEdit on a logic image containing everything BdL needs from the AFP (built on first use), so the BdL theories themselves can be opened and stepped through.

## Troubleshooting

- **Isabelle cannot find the session `Ordinary_Differential_Equations`:** the AFP is not registered. Repeat step 2 and check that the path ends in `/thys`.
- **A `### Version mismatch` message, or errors inside AFP theories:** the AFP release does not match your Isabelle version. Download the AFP release for Isabelle2025-2.

## Citing

If you use BdL, please cite it. GitHub's "Cite this repository" button uses the metadata in `CITATION.cff`; the equivalent BibTeX is:

```bibtex
@misc{BdL2026,
  author       = {Yakoub Nemouchi and Peter Graf},
  title        = {{BdL} (Biological Differential Dynamic Logic: A Formal Analyzer of
                  Dynamical Systems using Deductive Proofs for Biological Computing
                  and its Applications)},
  howpublished = {National Laboratory of the Rockies (NLR), Software Record SWR 26-101},
  year         = {2026},
  url          = {https://github.com/NatLabRockies/BdL}
}
```

## Background and related work

BdL mechanizes proof rules of André Platzer's differential dynamic logic (dL) in Isabelle/HOL. It builds on, and relates to, the following work.

**Differential dynamic logic**

- A. Platzer. Differential dynamic logic for hybrid systems. *Journal of Automated Reasoning* 41(2):143–189, 2008. [doi:10.1007/s10817-008-9103-8](https://doi.org/10.1007/s10817-008-9103-8)
- A. Platzer. *Logical Analysis of Hybrid Systems: Proving Theorems for Complex Dynamics.* Springer, 2010. [doi:10.1007/978-3-642-14509-4](https://doi.org/10.1007/978-3-642-14509-4)
- A. Platzer. A complete uniform substitution calculus for differential dynamic logic. *Journal of Automated Reasoning* 59(2):219–265, 2017. [doi:10.1007/s10817-016-9385-1](https://doi.org/10.1007/s10817-016-9385-1)
- A. Platzer. *Logical Foundations of Cyber-Physical Systems.* Springer, 2018. [doi:10.1007/978-3-319-63588-0](https://doi.org/10.1007/978-3-319-63588-0)

**Theorem provers for dL**

- A. Platzer and J.-D. Quesel. KeYmaera: A hybrid theorem prover for hybrid systems (system description). In *IJCAR 2008*, LNCS 5195, pp. 171–178. Springer, 2008. [doi:10.1007/978-3-540-71070-7_15](https://doi.org/10.1007/978-3-540-71070-7_15)
- N. Fulton, S. Mitsch, J.-D. Quesel, M. Völp, and A. Platzer. KeYmaera X: An axiomatic tactical theorem prover for hybrid systems. In *CADE-25*, LNCS 9195, pp. 527–538. Springer, 2015. [doi:10.1007/978-3-319-21401-6_36](https://doi.org/10.1007/978-3-319-21401-6_36)

**dL in Isabelle/HOL**

- R. Bohrer, V. Rahli, I. Vukotic, M. Völp, and A. Platzer. Formally verified differential dynamic logic. In *CPP 2017*, pp. 208–221. ACM, 2017. [doi:10.1145/3018610.3018616](https://doi.org/10.1145/3018610.3018616). Formalization: AFP entry [Differential_Dynamic_Logic](https://www.isa-afp.org/entries/Differential_Dynamic_Logic.html).

**Differential equations in dL: invariance, stability, liveness, and switched systems**

- A. Platzer and Y. K. Tan. Differential equation invariance axiomatization. *Journal of the ACM* 67(1), Article 6, 2020. [doi:10.1145/3380825](https://doi.org/10.1145/3380825)
- Y. K. Tan and A. Platzer. Deductive stability proofs for ordinary differential equations. In *TACAS 2021*, LNCS 12652, pp. 181–199. Springer, 2021. [doi:10.1007/978-3-030-72013-1_10](https://doi.org/10.1007/978-3-030-72013-1_10)
- Y. K. Tan and A. Platzer. An axiomatic approach to existence and liveness for differential equations. *Formal Aspects of Computing* 33(4):461–518, 2021. [doi:10.1007/s00165-020-00525-0](https://doi.org/10.1007/s00165-020-00525-0)
- Y. K. Tan, S. Mitsch, and A. Platzer. Verifying switched system stability with logic. In *HSCC 2022*, Article 2. ACM, 2022. [doi:10.1145/3501710.3519541](https://doi.org/10.1145/3501710.3519541)

**Ordinary differential equations in Isabelle/HOL**

- F. Immler and J. Hölzl. Ordinary Differential Equations. *Archive of Formal Proofs*, April 2012. <https://isa-afp.org/entries/Ordinary_Differential_Equations.html>

## Authors

- Yakoub Nemouchi, National Laboratory of the Rockies (NLR), Golden, CO, USA
- Peter Graf, National Laboratory of the Rockies (NLR), Golden, CO, USA

See [CONTRIBUTORS](CONTRIBUTORS).

## License

BdL is released under the BSD 3-Clause License; see [LICENSE](LICENSE).

Copyright © 2026 Alliance for Energy Innovation, LLC.
