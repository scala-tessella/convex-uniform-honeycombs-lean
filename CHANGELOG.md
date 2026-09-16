# Changelog

All notable changes to this formalization are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [Unreleased]

Initial development: the pen-and-paper core of *The 28 convex uniform honeycombs: a completeness
theorem*, formalized in Lean 4 over Mathlib (toolchain v4.33.1, Mathlib v4.33.1).

### Added

- `TwoTier.lean`: `cos 2α = -1/3`; `α = arctan √2` is not a rational multiple of `π` (Niven);
  the two-tier split of a lattice angle sum; the octet-support arithmetic of Corollary 5.4.
- `Tails.lean`: Lemmas A, B and E from the closed-form antiprism dihedrals, with the interleaving
  proved for every real `q ≥ 4` from `sin x < x`, `x - x³/6 < sin x`, `1 - x²/2 ≤ cos x` and
  `π < 3.15` — the paper's grid check is superseded.
- `Icosahedral.lean`: Identity I2 from the three exact cosines, with no interval.
- `Forcing.lean`: forcing along the edges of a connected graph (Theorem 5.9, Lemma 6.9) and the
  rebasing invariance of the canonical fingerprint (Lemma 6.7).
- `Periodization.lean`: the constants chain (Remark 6.2), the seam step, box rigidity (Lemma 6.5).

Every result is `sorry`-free and `native_decide`-free, depending at most on `propext`,
`Classical.choice` and `Quot.sound`.
