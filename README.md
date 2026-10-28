# The sofa problem in a snake-shaped corridor: Lean proof and numerical checks

This repository accompanies the paper *An upper bound of 2√2 for the three-dimensional sofa problem in a
snake-shaped corridor* by Tejasvi Singh Tomar. It contains a Lean 4 formalization of the main results
(`lean/`), optional numerical checks (`scripts/`, `explore/`) and the LaTeX source of the paper (`paper/main.tex`).

## What the paper proves

The corridor K_M has unit-square cross-section, an entry arm along the x-axis, a middle arm along the
y-axis with a straight section of length M, and an exit arm along the z-axis. Its two turns lie in the
x–y and y–z planes. This is Problem 6.64 of Georgiev, Gómez-Serrano, Tao and Wagner (arXiv:2511.02864),
whose code uses M = 4.

- **Theorem 1.1.** For every M > 2 + √2, every compact connected body that can be moved through K_M by a
  continuous family of rigid motions has volume at most 2√2 = 2.8284… . Remark 2.3 and Corollary 4.6 of
  the paper extend this to bounded connected sets, stronger notions of passage and the corridor with one turn.
- **Lemma 3.3.** Two tubes of unit-square cross-section whose axes make an angle θ meet in volume at most
  1/sin θ. The bound is sharp.
- **Corollary 5.1.** For √2 < M ≤ 2 + √2, the volume is at most
  Γ(M) = (M² + 2)/(M² − 2) + (M² + 2)/(2√2 M). This is below Tang's bound 3.4083 for 2.26 ≤ M ≤ 2 + √2.
- **Proposition 6.1.** The relaxation used at a single time in the proof has the exact value
  1/s + 1/√(1 − s²) ≥ 2√2, so this argument cannot give a bound below 2√2.

The proofs in Sections 2–6 of the paper are analytic and use no computer. The main results are also proved in
Lean 4 with Mathlib (next section). The scripts after that are optional numerical sanity checks of the lemmas and of the
chain of inequalities in the proof. No step of the paper depends on them.
The numerical observations in Section 7 of the paper (relaxations with several times, as in Remark 6.3) come from
the exploratory code in `explore/`, described at the end of this file.

## Lean formalization (`lean/`)

The directory `lean/` is a Lean 4 project for Lean `v4.35.0-rc3` (file `lean-toolchain`) and Mathlib at tag
`v4.35.0-rc3`, commit `c55e6e786f49` (file `lake-manifest.json`). Every theorem below depends only on the standard
axioms `propext`, `Classical.choice` and `Quot.sound`. The files contain no `sorry`, no further axioms and no
`native_decide`. In a separate check, the proofs were rebuilt from a clean copy of the sources on another machine,
and `leanchecker` and the kernels nanoda and lean4lean accepted the exported proofs. The check used the
`leanchecker` of the `v4.35.0-rc3` toolchain, nanoda 0.4.17, and lean4lean built against Lean
4.35.0-nightly-2026-09-06 and run on the export.

| Theorem | Statement | Paper |
|---|---|---|
| `Sofa3D.main` | For every M > 2 + √2, V\*(K_M) ≤ 2√2. | Theorem 1.1 |
| `Sofa3D.weak` | The same bound for every body moved by a continuous family of rigid motions that satisfies only the conditions (i), (ii′) and (iii′) of Remark 2.3. | Remark 2.3 |
| `Sofa3D.bounded` | The same bound for the outer measure of every bounded connected set with a passage. | Remark 2.3 |
| `Sofa3D.chord_sq_le_one` | ∫ ℓ(b)² db ≤ 1 for the chord function ℓ of the square [−1/2, 1/2]² and every orthonormal pair (m, n). | Lemma 3.2 (the bound) |
| `Sofa3D.two_tube` | Two tubes at angle θ ∈ (0, π/2] meet in volume at most 1/sin θ. | Lemma 3.3 (the bound) |
| `Sofa3D.tilt` | If a tube with axis direction w meets W_1 and W_{1+u}, u > √2, then \|w·e_y\| ≥ μ\*(u). | Lemma 4.3 |
| `Sofa3D.prop45` | For √2 < u < M and 0 < s ≤ μ\*(u), a body moved as in the row `weak` has volume at most 1/s + 1/√(1 − s²). | Proposition 4.5 |
| `Sofa3D.short` | For √2 < M ≤ 2 + √2, V\*(K_M) ≤ Γ(M). | Corollary 5.1 |
| `Sofa3D.main_ge` | The bound of Theorem 1.1 for every M ≥ 2 + √2. | Remark 5.2(a) |
| `Sofa3D.relax` | For 0 < s < 1 and c ≥ 1 + (1 + s)/√(1 − s²), the largest volume of T ∩ (S_X ∪ S_Y(c)) over tubes T with \|w·e_y\| = s is 1/s + 1/√(1 − s²) (bound and a tube attaining it). | Proposition 6.1 |
| `Sofa3D.relax_value` | For 0 < s < 1, 1/s + 1/√(1 − s²) ≥ 2√2, with equality if and only if s = 1/√2. | Proposition 6.1 |
| `Sofa3D.one_le_Vstar` | V\*(K_M) ≥ 1 for M ≥ 0: the unit cube passes by translations, so the definitions admit passages. | Appendix A |

The definitions of the corridor, bodies, passages and V\* are in `Sofa3D/Defs.lean`, and the statements of the
table are in `Sofa3D/Statements.lean` or next to their proofs. The chord function (`Chord.lean`), the windows W_c
(`Tilt.lean`) and μ\* (`Main.lean`) are defined in the proof files. Points of ℝ³ are functions `Fin 3 → ℝ`, the
measure is Mathlib's Lebesgue measure, V\* takes values in [0, ∞], and the rotation part of a passage lies in
SO(3) at every time. The modules follow the paper: `Chord` (Lemma 3.2), `Frame` (orthonormal frames and
integration in a frame), `TwoTube` (Lemma 3.3), `Tilt` (Lemma 4.3), `Rigid` (rigid motions map tubes to tubes and
preserve volume; the tubes X and Y), `Crossing` (facts about the corridor, and the reduction to g_0 = id), `Main` (Proposition 4.5,
Theorem 1.1 and its extension in Remark 2.3, Corollary 5.1, Remark 5.2(a)), `Extras` (the last sentence of Proposition 6.1, bounded sets),
`Relax` (Proposition 6.1) and `NonVacuity`. Lemmas 4.1 and 4.2 and the inclusions K_M ∩ {y ≤ c} ⊆ S_X ∪ S_Y(c) ⊆ X ∪ Y of
(2.1) are proved only as steps of the proof of Proposition 4.5. Not formalized: the equality cases of Lemmas 3.2 and 3.3, Remarks 3.4, 4.4,
5.2(b)–(c) (with Table 1) and 6.2–6.4, the paragraph after Proposition 6.1, the other statements of Remark 2.3 (passages
through the interior of K_M, the end positions of the code of Georgiev et al.) and Corollary 4.6 (the corridor with one turn).

To check the proofs, install elan (the Lean toolchain manager) and run, from `lean/`:

```
lake exe cache get                # downloads the compiled Mathlib for this commit
lake build Sofa3D                 # one to two minutes on 32 cores; peak memory about 7 GB
lake env lean tools/Axioms.lean   # checks the statements and prints the axioms
```

The last command checks the seven statements of `Sofa3D/Statements.lean` against their theorems, prints the
statements of the other five theorems, and prints the axioms of all twelve; compare with
`expected/lean_axioms.out`.

## Requirements

For the scripts: Python 3 with numpy and scipy. `chord_integral.py` also needs sympy, and `check_constants.py` needs
python-flint. The expected outputs in `expected/` were produced with numpy 2.5.4, scipy 1.18.1 and
python-flint 0.9.0 on Python 3.12, and with sympy 1.14.0 on Python 3.14 for `chord_integral.py`. Other
versions may change the last digits of the floating-point output.

## Scripts

All scripts are in `scripts/` and print their results to standard output. `geom.py` holds shared helpers:
tubes and boxes as systems of linear inequalities, exact volumes of the resulting polytopes (scipy's
HalfspaceIntersection and ConvexHull, that is, qhull), and chord lengths of a square.

| Script | What it checks | Run time on one core |
|---|---|---|
| `chord_integral.py` | Lemma 3.2. Exact chord function of the unit square (sympy), its area 1, the closed form (cos ψ − sin(ψ)/3)/cos² ψ of the squared-chord integral for 0 ≤ ψ ≤ π/4, the positivity of 1 − f through the cubic 3t³ + t² − 3t + 1 (t = tan(ψ/2)), and a sweep over 400 angles. | about 70 s |
| `two_tubes.py` | Lemma 3.3. Exact intersection volumes against the slicing formula of the proof, and a Nelder–Mead maximization of vol(T ∩ T′)·sin θ over all 12 placement parameters (largest value 0.9999999998). | about 2–4 min |
| `two_tubes_mc.py` | Monte Carlo cross-check of the exact intersection volumes. | about 30 s |
| `tilt.py` | Lemma 4.3. Minimizes the tilt \|w·e_y\| over all tubes that meet the windows W_1 and W_{1+u}; the minimum equals μ*(u) = (u² − 2)/(u² + 2) to about 1e-12. | about 45 s |
| `single_pose.py` | Proposition 6.1 and the last step of the proof of Proposition 4.5. Checks vol(T ∩ (S_X ∪ S_Y(c))) ≤ vol(T ∩ X) + vol(T ∩ Y) ≤ 1/sin θ_x + 1/sin θ_y on random tubes, finds the value 2√2 at tilt 1/√2 that Proposition 6.1 proves to be the maximum, and sweeps other tilts s against 1/s + 1/√(1 − s²) (c = 4.5). | about 6–7 min |
| `record_path.py` | The chain of inequalities in the proof of Theorem 1.1 on a concrete motion through both turns of K_4: the 512-pose record path from Tang's repository. | about 55 s |
| `hammersley_sofa.py` | The same chain on Hammersley's sofa extruded by 1 in the z-direction, moved by Hammersley's motion. | about 8 s |
| `check_constants.py` | Interval arithmetic (arb balls from python-flint). The inequality of Lemma 3.2 on [10⁻³, π/4] by 20000 cells, with a Taylor bound near 0; μ*(2 + √2) = 1/√2; the values Γ(2) < 4.061, Γ(2.26) < 3.4083, Γ(2.3) < 3.337, Γ(2.61) < 3.025 and Γ(3) < 2.868 of Remark 5.2; and 2√2 < 2.8285. | under 1 s |

In the scripts, `SX`, `Stub(c)`, `X_w` and `Y_w` denote the sets S_X, S_Y(c), X and Y of the paper,
`tau_c` is the time τ of Lemma 4.2, and `t*` is the time t in the proof of Proposition 4.5.

Notes on the output.

- In `chord_integral.py`, the numerical sweep reports a largest squared-chord integral of 1.000050. This
  is the error of the trapezoid rule at the kinks of the chord function. The exact value is at most 1
  (Lemma 3.2), with equality only for chords parallel to a side.
- In `two_tubes.py`, some Nelder–Mead starts report 0 because they begin and stay at disjoint tubes.
- In `single_pose.py`, the sweep value at s = 0.9 lies below 1/s + 1/√(1 − s²) because the height c = 4.5
  is smaller than the height 1 + (1 + s)/√(1 − s²) ≈ 5.36 that Proposition 6.1 assumes.

## How to run

From the root of this repository:

```
python3 -I scripts/chord_integral.py
python3 -I scripts/two_tubes.py            # optional argument: number of Nelder-Mead starts (default 24)
python3 -I scripts/two_tubes_mc.py
python3 -I scripts/tilt.py 2.2 2.6 3.414213562373095 3.5 3.9
python3 -I scripts/single_pose.py          # optional argument: number of starts (default 40)
python3 -I scripts/record_path.py PATH/TO/w6_night3_final_iterate.npy    # optional: h (0.025), SUB (6)
python3 -I scripts/hammersley_sofa.py      # optional argument: grid step h (default 0.01)
python3 -I scripts/check_constants.py
```

`record_path.py` needs the file `data/w6_night3_final_iterate.npy` from Tang's repository
<https://github.com/Lomnus-ai/sofa3d-upper-bound>, which is not included here. The script loads it with
`allow_pickle=False`.

Compare the output with the files in `expected/`.

## Exploratory code behind Section 7 (`explore/`)

The directory `explore/` holds exploratory floating-point code. It is not rigorous, and the paper uses its
output only for the numerical observation in Section 7, where the largest value found is stated as the best
local maximum found numerically. The searches use Nelder–Mead from random starting points with fixed seeds.

| Script | What it does | Run time on one core |
|---|---|---|
| `scan3.py` | Planar version of the relaxation with several times, with natural orientations (same rotation sense, no reflection, no reversal of the axis) and the stub height c = 5 (for M = 4 the angle 51° needs c ≥ 4.9936…, and a larger c can only increase the relaxation): best local maximum found from 25 starts (seed 0) for each tuple of angles. Output: 2.54313 for the angles (51°, 30°), and 2.48013, 2.47944, 2.48073 for (51°, 38°, 22°), (51°, 35°, 20°), (51°, 36°, 18°). | about 30 s |
| `multi_ev2.py` | The same relaxation (c = 5) in three dimensions, with the angles +51° and +30°: tilt of the axis out of the x–y plane with \|w_z\| ≤ 0.95, free roll about the axis, and offsets (9 parameters for two times). For seeds 1–4 with 12 starts each, the best value is 2.54313 every time, at a planar configuration (no tilt, rolls multiples of π/2, centred in z). Some starts stop at lower values, also at non-planar points; these are stalls of the search, not better configurations. | about 4–5 min per seed |
| `signs.py` | Planar relaxation with the sign of each angle and a roll of the body by π (a reflection in the planar picture) chosen independently, c = 5, best local maximum from 80 starts (seed 2). The listed runs keep the first time unrolled; this loses nothing, because a reflection of the body frame changes all rolls at once. For the angles 51° and 30°: 2.543127 with both signs positive and no roll, and at most 1.922250 for every other choice; single times: 2.875775 (+51°), 1.589016 (−51°), 3.154701 (+30°), 2.000000 (−30°). | about 2–4 min for all twelve cases |
| `planar2d.py` | Planar helpers used by `scan3.py`: polygon clipping, areas, connected components. Its own search tries all eight orientations per time (sign of the angle, roll by π, reversal of the axis); the relaxation of Remark 6.3 excludes reversal of the axis. | |
| `multi_ev.py`, `poly3.py` | Helpers used by `multi_ev2.py`: polytope volumes from half-spaces and the corridor pieces. | |

```
python3 -I explore/scan3.py 51,30 51,38,22 51,35,20 51,36,18
python3 -I explore/multi_ev2.py 12 4000 1 51 30     # repeat with seeds 2, 3 and 4 in place of the third argument
python3 -I explore/signs.py 5.0 80 2 51 30          # also with 51 30r, 51 -30, 51 -30r, -51 30, -51 30r, -51 -30, -51 -30r, 51, -51, 30, -30
```

Expected outputs: `expected/explore_scan3.out`, `expected/explore_multi_ev2_s1.out` to `_s4.out`, and `expected/explore_signs.out`.

## License and citation

The Lean files and the scripts are released under the Apache License 2.0 (see `LICENSE`), and the LaTeX source of the paper
under CC BY 4.0. Please cite the paper; see `CITATION.cff`.
