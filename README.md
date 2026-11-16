# Graded neighborhoods based on an ideal – computations

Wolfram Language (Mathematica) code for the computations in the paper
**"Approximation Spaces Based on Graded Neighborhoods via Two Ideals and Their Applications"**.

## Contents

| File | Purpose |
|------|---------|
| `graded_neighborhoods.wl` | All computations of the paper (Parts A, B, C below). |
| `graded_check.py` | An independent Python implementation of the same computations, used as a cross-check. |

## Requirements

Mathematica 12 or later, or the free Wolfram Engine with `wolframscript`.
No packages are needed. The script was run on Wolfram Language 15.0.1 (Linux x86, 64-bit): Parts A, B and C
produce the outputs described below.

## Usage

```bash
wolframscript -file graded_neighborhoods.wl
```

or, inside Mathematica, `Get["graded_neighborhoods.wl"]`.

## What the script does

* **Part A – Example 31.** The universe is `{a, b, c, d}`. For every nonempty subset `A` it computes the lower
  approximation, the upper approximation and the accuracy for four models: Kozae et al., Kandil et al., the second pair
  of Kandil et al. (2020), and the present model (graded neighborhood). The 60 entries are compared with Table 4 of the paper.
* **Part B – application.** Ten objects of the Breast Cancer (Ljubljana) data, coded as in Table 5 of the paper.
  The script builds the relation `R`, the neighborhoods `N(x)`, the ideal `Y` (the two objects farthest from the median
  profile), the graded neighborhoods `N^I(x)`, and the rows of Table 6 (approximations of the two decision classes, mean
  accuracy, dependency degree, mean neighborhood size, mean accuracy over all nonempty subsets, number of open sets).
  The values are compared with the paper.
* **Part C – random checks.** On 400 random finite relations (3 to 5 points) it checks the properties proved in the
  paper: the inclusions `N^I ⊆ N ⊆ ⟨x⟩R`, the equality neighborhood for the trivial ideal, nestedness, monotonicity in
  the ideals, duality, additivity, idempotency, the boundary as frontier, the topology and its comparison with the
  topologies of the earlier models, and the special cases (`I = P(X)`; preorders).

## Conventions

* The universe is `{1, …, n}`; sets are sorted lists; a relation is a list of pairs `{x, y}` meaning `x R y`.
* In a finite universe every ideal is principal, `I = P(Y)`, so an ideal is represented by the set `Y`:
  `B ∈ I` iff `B ⊆ Y`.
* Notation of the code and of the paper:

| Code | Paper |
|------|-------|
| `neighborhoods[rel, X]["N"]` | `N(x) = ⟨x⟩R ∩ R⟨x⟩` |
| `graded[N, X, struct]` | graded neighborhood `N^I(x) = { y ∈ N(x) : N(x) \ N(y) ∈ I }`, `I = P(struct)` |
| `lowerJ[M, A, test]`, `upperJ[M, X, A, test]` | lower and upper approximations with the test ideal `J = P(test)` |
| `yaoLower`, `yaoUpper` | approximations of Yao type (test ideal `{∅}`) |
| `openSets[M, X, test]` | open sets of the induced topology |

## Expected output

* Part A: `Part A: all 60 entries agree with Table 4 of the paper.`
* Part B: `Y = {o8, o9}` and the following rows of Table 6.

| model | acc. | γ | mean \|M(x)\| | acc. (subsets) | open sets |
|-------|------|---|--------------|----------------|-----------|
| Allam et al. | 0.000 | 0.0 | 6.00 | 0.044 | 7 |
| Kozae et al. | 0.200 | 0.4 | 2.70 | 0.231 | 43 |
| Kandil et al. | 0.050 | 0.1 | 6.00 | 0.126 | 25 |
| second pair of Kandil et al. (2020) | 0.200 | 0.4 | 2.70 | 0.264 | 77 |
| present | 0.657 | 0.8 | 1.60 | 0.658 | 320 |

* Part C: `violations: none`.

## Citation

Please cite the paper (reference to be added after publication).
