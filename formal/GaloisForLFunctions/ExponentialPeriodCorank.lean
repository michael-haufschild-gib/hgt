/-
# The exponential-period corank: reducing Stieltjes irrationality to integer linear forms

The archimedean regularization constants of `ζ` at its pole `s = 1` — the Stieltjes constants, of
which `γ₀ = eulerMascheroniConstant` is the first — are the "non-period" side of the seam
`ξ = (Γ-factor)·ζ`: conjecturally exponential periods, independent of the period algebra of the
convergent `ζ`-values `{ζ(k)}_{k≥2} = {(1/j!)·∫₀^∞ tʲ/(eᵗ−1)\,dt}`. The apex question (does the
non-period side escape the period field) rests, at its weakest necessary point, on the irrationality
of `eulerMascheroniConstant`.

This file formalizes the **mechanism** by which such irrationality/independence is decided — the
integer-linear-forms criterion (the engine behind Rivoal–Ball / Nesterenko / Apéry) — and thereby
reduces the open atom to an explicit *construction* problem:

* `irrational_of_linearForms` — if integer forms `pₙ + qₙ·α` are nonzero and tend to `0`, then `α`
  is irrational (a nonzero rational with bounded denominator is bounded away from `0`).
* `not_all_rat_of_linearForms` — the family version: nonzero integer forms `aₙ + Σᵢ bₙᵢ·xᵢ` tending
  to `0` force some `xᵢ` irrational (the form is a nonzero rational of denominator dividing the fixed
  product of the `xᵢ`-denominators, hence `≥ 1/D`).
* `eulerMascheroniConstant_irrational_of_linearForms` — the atom, localized: `γ₀` is irrational as
  soon as such integer forms exist.

The reason the construction resists (the analytic core of the open problem, not formalizable
unconditionally): the natural approximants `harmonic n − log n → γ₀` (`Real.tendsto_harmonic_sub_log`)
carry the transcendental `log n`, so they are *not* integer forms in `γ₀`; and the coefficient-
extraction forms `∮ (ζ(1+z) − 1/z) Q(z)\,dz` are dominated by the factorial `Γ`-factor of the
functional equation, obstructing the required smallness. Producing genuine integer forms in the
Stieltjes constants — defeating the `log`/`Γ` entanglement — is the irreducible open input; the
criterion below is the exact interface it must feed.
-/
import Mathlib

open Filter Topology

namespace GaloisForLFunctions

/-- **Integer-linear-forms irrationality criterion.**  If there are integer linear forms
`pₙ + qₙ·α` that are nonzero for every `n` and tend to `0`, then `α` is irrational.  Were `α = c`
rational, each form would be `mₙ / c.den` with `mₙ ∈ ℤ` nonzero, hence `|·| ≥ 1/c.den > 0`,
contradicting convergence to `0`.  This is the engine of the Rivoal–Ball/Nesterenko method. -/
theorem irrational_of_linearForms (α : ℝ) (p q : ℕ → ℤ)
    (hne : ∀ n, (p n : ℝ) + (q n : ℝ) * α ≠ 0)
    (h0 : Tendsto (fun n => (p n : ℝ) + (q n : ℝ) * α) atTop (𝓝 0)) :
    Irrational α := by
  rintro ⟨c, hc⟩
  set d : ℤ := (c.den : ℤ) with hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by rw [hd]; exact_mod_cast c.pos
  have hαeq : α = (c.num : ℝ) / (d : ℝ) := by
    rw [← hc, hd]; push_cast [Rat.cast_def]; ring
  have key : ∀ n, (p n : ℝ) + (q n : ℝ) * α
      = ((p n * d + q n * c.num : ℤ) : ℝ) / (d : ℝ) := by
    intro n; rw [hαeq]; field_simp; push_cast; ring
  have hlb : ∀ n, (1 : ℝ) / (d : ℝ) ≤ |(p n : ℝ) + (q n : ℝ) * α| := by
    intro n
    have hmn : (p n * d + q n * c.num : ℤ) ≠ 0 := by
      intro hz; apply hne n; rw [key n, hz]; norm_num
    have h1 : (1 : ℝ) ≤ |((p n * d + q n * c.num : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hmn
    rw [key n, abs_div, abs_of_pos hdpos]; gcongr
  have habs : Tendsto (fun n => |(p n : ℝ) + (q n : ℝ) * α|) atTop (𝓝 0) := by
    simpa using h0.abs
  obtain ⟨n, hn⟩ :=
    (habs.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (d : ℝ)))).exists
  exact absurd (hlb n) (not_le.mpr hn)

/-- **Family linear-forms criterion.**  If there are integer linear forms `aₙ + Σᵢ bₙᵢ·xᵢ` in a
finite family `x : Fin k → ℝ`, nonzero for every `n` and tending to `0`, then the `xᵢ` are **not all
rational**.  Were every `xᵢ = rᵢ ∈ ℚ`, each form would be a rational of denominator dividing the fixed
`D = ∏ᵢ (rᵢ).den`, i.e. `mₙ / D` with `mₙ ∈ ℤ` nonzero, hence `|·| ≥ 1/D`, contradicting convergence
to `0`.  This is the joint (independence-flavored) form of the criterion, the shape a DSS-cross-style
attack on the whole Stieltjes family would feed. -/
theorem not_all_rat_of_linearForms {k : ℕ} (x : Fin k → ℝ) (a : ℕ → ℤ) (b : ℕ → Fin k → ℤ)
    (hne : ∀ n, (a n : ℝ) + ∑ i, (b n i : ℝ) * x i ≠ 0)
    (h0 : Tendsto (fun n => (a n : ℝ) + ∑ i, (b n i : ℝ) * x i) atTop (𝓝 0)) :
    ¬ ∀ i, ∃ r : ℚ, x i = (r : ℝ) := by
  rintro hrat
  choose r hr using hrat
  set D : ℤ := ∏ i, ((r i).den : ℤ) with hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by
    rw [hD]; push_cast
    exact Finset.prod_pos fun i _ => by exact_mod_cast (r i).pos
  have hDr : ∀ i, ∃ z : ℤ, (r i : ℝ) * (D : ℝ) = (z : ℝ) := by
    intro i
    refine ⟨(r i).num * ∏ j ∈ Finset.univ.erase i, ((r j).den : ℤ), ?_⟩
    rw [hD, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    push_cast [Rat.cast_def]; field_simp
  choose z hz using hDr
  set mfun : ℕ → ℤ := fun n => a n * D + ∑ i, b n i * z i with hm
  have key : ∀ n, ((a n : ℝ) + ∑ i, (b n i : ℝ) * x i) = (mfun n : ℝ) / (D : ℝ) := by
    intro n
    rw [hm]; push_cast; rw [add_div, Finset.sum_div]
    congr 1
    · field_simp
    · exact Finset.sum_congr rfl fun i _ => by rw [hr i, ← hz i]; field_simp
  have hlb : ∀ n, (1 : ℝ) / (D : ℝ) ≤ |(a n : ℝ) + ∑ i, (b n i : ℝ) * x i| := by
    intro n
    have hmn : mfun n ≠ 0 := by
      intro hzero; apply hne n; rw [key n, hzero]; norm_num
    have h1 : (1 : ℝ) ≤ |((mfun n : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hmn
    rw [key n, abs_div, abs_of_pos hDpos]; gcongr
  have habs : Tendsto (fun n => |(a n : ℝ) + ∑ i, (b n i : ℝ) * x i|) atTop (𝓝 0) := by
    simpa using h0.abs
  obtain ⟨n, hn⟩ :=
    (habs.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / (D : ℝ)))).exists
  exact absurd (hlb n) (not_le.mpr hn)

/-- **The atom, localized.**  The irrationality of the Euler–Mascheroni constant `γ₀` — the weakest
necessary point of the entire DSS/exponential-period apex — follows from the existence of nonzero
integer linear forms `pₙ + qₙ·γ₀` tending to `0`.  This machine-checks the reduction "irrationality of
`γ₀` ⟸ construct the forms"; the construction is the open input, obstructed by the `log`/`Γ`
entanglement documented above. -/
theorem eulerMascheroniConstant_irrational_of_linearForms (p q : ℕ → ℤ)
    (hne : ∀ n, (p n : ℝ) + (q n : ℝ) * Real.eulerMascheroniConstant ≠ 0)
    (h0 : Tendsto (fun n => (p n : ℝ) + (q n : ℝ) * Real.eulerMascheroniConstant) atTop (𝓝 0)) :
    Irrational Real.eulerMascheroniConstant :=
  irrational_of_linearForms _ p q hne h0

end GaloisForLFunctions
