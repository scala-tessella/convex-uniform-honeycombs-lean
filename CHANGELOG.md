# Changelog

All notable changes to this formalization are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/).

## [0.4.0] — 2026-09-21

The pen-and-paper addition of the paper's v0.9 revision: the Euclidean core of the cell rigidity lemma.

### Added

- `CellRigidity.lean`: the cell rigidity lemma of the paper (Section 6.1, the correction of the fifth
  revision — a placed core cell is determined by its type, one edge, the two face germs there and their
  roles) rests on three finite facts certified in the artifact and on one piece of Euclidean geometry,
  proved here: a linear isometry that fixes or reverses the direction `d` of a segment and maps each of two
  interior directions `p₁, p₂` (perpendicular to `d`, spanning the space with it) into its own plane
  `span {d, pᵢ}` on its own side (`⟪L pᵢ, pᵢ⟫ > 0`) is the identity or the reflection in the plane
  perpendicular to `d` (`wedge_isometry`, from `interior_fixed`, `eq_of_fixes_three` and the explicit
  `bisectorReflection` with its involution).

## [0.3.0] — 2026-09-20

The periodization section brought in line with the paper's v0.6–v0.7 proof, in which condition (P) is a
direct reduction to the box (two clauses) and the seam walk is gone.

### Changed

- `Periodization.lean`: `constants_table` replaces `constants_chain` — the three lines of Remark 7.2 as it now
  stands (`covB + max|τ| < R_per`, `covB + 1 ≤ R_per − 1/2`, `R_per − 1/2 + 1 < R_per + 8/5`); the
  earlier chain with the `2.6` reach described a step that condition (G) removed. `seam_coefficient` is
  kept for the record but no longer corresponds to a step of the proof.

### Added

- `Periodization.lean`: the box representative of condition (P) — `roundHalfUp`, `remainder_mem`
  (remainders in `[-1/2, 1/2)`), `remainder_add_int` (the same representative for a whole lattice
  orbit); and `entries_eq_periodization_on_ball`, the field identification: from the two clauses of (P),
  the ball entries and the vertices of the periodization within the ball coincide, with the developed
  star field the periodized one there — the step the referee's last two corrections were about.

## [0.2.0] — 2026-09-20

The pen-and-paper additions of the paper's v0.5 revision.

### Added

- `Tails.lean`, section *Corridors*: `a₃q` is antitone and `a₃₃` monotone on `[4, ∞)`, whence the
  tail corridors of the uncapped corona fixpoint (Section 4.1) — for every real `q ≥ 301`,
  `a₃q(q) ∈ (π/2, a₃q(301)]` and `a₃₃(q) ∈ [a₃₃(301), π)`, and for every real `p ≥ 501` the prism
  lateral `π - 2π/p ∈ [π - 2π/501, π)`. These are the hypotheses under which a completion through a
  tail cell is a completion over the corridor, so that the fixpoint's pool has no cap.
- `Separation.lean`: the separation constant of the species search (Lemma 5.2) is exact — the
  altitude of the tetrahedral corner, the angle whose sine is `√(2/3)`, is `α = arctan √2`, the
  generator of the two-tier lattice. Proved on explicit coordinates of the corner figure (three unit
  vectors pairwise at `60°`): the squared sine of the vertex-to-opposite-side distance is `2/3`, and
  `sin² α = 2/3` from `cos 2α = -1/3`. The sweep showing no other corner does worse stays an interval
  computation in the artifact.

## [0.1.0] — 2026-09-19

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
