/-
# Finite clockwork cannot manufacture an aperiodic limit zero

A vertical arithmetic progression of zeros `{w + kTi : k ∈ ℤ}` is the trace of a *clock* of
period `T`: the carrier is invariant under the vertical shift `s ↦ s + Ti`. When a family of
carriers `Fₙ` runs a clock at each of its zeros with the period drawn from one *fixed finite
inventory* `𝒯 ⊆ ℝ`, that structure survives passage to a locally uniform limit. Concretely: if
`Fₙ → F` locally uniformly on a vertically-shift-closed domain `Ω`, if zeros `zₙ` of `Fₙ` ride a
full two-sided progression of `Fₙ`-zeros of period `Tₙ ∈ 𝒯`, and if `zₙ → z ∈ Ω`, then the limit
point `z` rides a full two-sided progression of `F`-zeros whose period again lies in `𝒯`.

The proof is pigeonhole followed by a limit exchange. The inventory `𝒯` is finite, so some period
`T` recurs along an infinite subsequence of indices; on that subsequence every `Fₙ` carries the
progression of the *same* period `T`. Fixing the step `k`, the shifted points
`zₙ + (kT)i` converge to `z + (kT)i` inside `Ω`, and locally uniform convergence composed with a
convergent sequence of arguments sends the value `Fₙ(zₙ + (kT)i) = 0` to `F(z + (kT)i)`; uniqueness
of limits pins the latter to `0`.

Contrapositive — the clock-escape statement: an *aperiodic* zero of `F` (a zero lying on no full
vertical progression of `F`-zeros) cannot be approximated by zeros of the `Fₙ` that ride
progressions from any fixed finite period inventory. The responsible clock must escape every finite
set. For an Euler product, whose finite-prime truncations are column forms carrying only the
progressions of periods `2π/log p` over the truncation primes, an aperiodic zero of the completed
limit therefore forces the responsible prime to leave every finite set: no bounded prime inventory
can host it.

The hypothesis that the approximating zeros exist and converge — Hurwitz's theorem for the carriers
in play — is carried here as an explicit input, not derived.
-/
import GaloisForLFunctions.RHTower.PeriodicityDichotomy
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Set.Finite.Lattice

namespace RHTower

open Complex Filter Topology Set

/-- A finite clockwork cannot create an aperiodic zero in the limit.

If carriers `Fₙ` converge locally uniformly to `F` on a domain `Ω` closed under vertical shifts,
each `Fₙ`-zero `zₙ` rides a full two-sided vertical progression of `Fₙ`-zeros whose period `Tₙ`
lies in a fixed finite set `𝒯`, and `zₙ → z ∈ Ω`, then `z` rides a full two-sided vertical
progression of `F`-zeros whose period also lies in `𝒯`.

Mechanism: `𝒯` is finite, so by the pigeonhole principle some `T ∈ 𝒯` equals `Tₙ` for infinitely
many `n`; extract a strictly increasing subsequence `φ` on which `Tₙ = T`. For each step `k`, the
subsequenced carriers still converge locally uniformly to `F`, the shifted arguments
`zₙ + (kT)i` converge to `z + (kT)i` within `Ω` (using shift-closure of `Ω`), and
`TendstoLocallyUniformlyOn.tendsto_comp` sends the constantly-zero values `Fₙ(zₙ + (kT)i)` to
`F(z + (kT)i)`; uniqueness of limits gives `F(z + (kT)i) = 0`. -/
theorem periodic_zero_limit {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ} {𝒯 : Finset ℝ}
    (hconv : TendstoLocallyUniformlyOn Fn F Filter.atTop Ω)
    (hFc : ContinuousOn F Ω)
    {z : ℂ} (hz : z ∈ Ω)
    {zn : ℕ → ℂ} (hzn : Filter.Tendsto zn Filter.atTop (nhds z)) (hznΩ : ∀ n, zn n ∈ Ω)
    {Tn : ℕ → ℝ} (hTn : ∀ n, Tn n ∈ 𝒯)
    (hper : ∀ n, ∀ k : ℤ, Fn n (zn n + (k * Tn n) * Complex.I) = 0) :
    ∃ T ∈ 𝒯, ∀ k : ℤ, F (z + (k * T) * Complex.I) = 0 := by
  classical
  -- Pigeonhole: some period `T ∈ 𝒯` is attained at infinitely many indices.
  have hpigeon : ∃ T ∈ 𝒯, {n | Tn n = T}.Infinite := by
    by_contra h
    have hfin : ∀ T ∈ 𝒯, {n | Tn n = T}.Finite := by
      intro T hT
      rw [← Set.not_infinite]
      exact fun hinf => h ⟨T, hT, hinf⟩
    have hcover : (Set.univ : Set ℕ) ⊆ ⋃ T ∈ (𝒯 : Set ℝ), {n | Tn n = T} := by
      intro n _
      exact Set.mem_biUnion (Finset.mem_coe.mpr (hTn n)) rfl
    have hbig : (⋃ T ∈ (𝒯 : Set ℝ), {n | Tn n = T}).Finite :=
      Set.Finite.biUnion 𝒯.finite_toSet (fun T hT => hfin T (Finset.mem_coe.mp hT))
    exact Set.infinite_univ (hbig.subset hcover)
  obtain ⟨T, hT, hinf⟩ := hpigeon
  refine ⟨T, hT, ?_⟩
  -- Extract a strictly increasing subsequence `φ` on which the period is exactly `T`.
  have hfreq : ∃ᶠ n in Filter.atTop, Tn n = T := Nat.frequently_atTop_iff_infinite.mpr hinf
  obtain ⟨φ, hφmono, hφspec⟩ := extraction_of_frequently_atTop hfreq
  have hφtends : Filter.Tendsto φ Filter.atTop Filter.atTop := hφmono.tendsto_atTop
  -- The subsequenced clockwork still converges locally uniformly to `F`.
  have hconv' : TendstoLocallyUniformlyOn (fun m => Fn (φ m)) F Filter.atTop Ω := by
    intro u hu x hx
    obtain ⟨t, ht, H⟩ := hconv u hu x hx
    exact ⟨t, ht, hφtends.eventually H⟩
  -- The convergent index sequence pulls back along `φ`.
  have hznφ : Filter.Tendsto (fun m => zn (φ m)) Filter.atTop (nhds z) := hzn.comp hφtends
  intro k
  -- Casting the real step `(k : ℝ) * T` into `ℂ` matches the complex progression step.
  have hcast : (((k : ℝ) * T : ℝ) : ℂ) = (k : ℂ) * (T : ℂ) := by push_cast; ring
  -- The target point of the progression lies in `Ω`.
  have hwΩ : z + (k : ℂ) * (T : ℂ) * Complex.I ∈ Ω := by
    have h := hΩshift z hz ((k : ℝ) * T); rw [hcast] at h; exact h
  -- Each shifted index point lies in `Ω`.
  have hgΩ : ∀ m, zn (φ m) + (k : ℂ) * (T : ℂ) * Complex.I ∈ Ω := by
    intro m
    have h := hΩshift (zn (φ m)) (hznΩ (φ m)) ((k : ℝ) * T); rw [hcast] at h; exact h
  -- The shifted index sequence converges to the target within `Ω`.
  have hg : Filter.Tendsto (fun m => zn (φ m) + (k : ℂ) * (T : ℂ) * Complex.I)
      Filter.atTop (𝓝[Ω] (z + (k : ℂ) * (T : ℂ) * Complex.I)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hznφ.add tendsto_const_nhds, Filter.Eventually.of_forall hgΩ⟩
  -- Locally uniform convergence composed with the convergent arguments.
  have hcomp := hconv'.tendsto_comp (hFc _ hwΩ) hwΩ hg
  -- Along the subsequence the composed values are identically zero.
  have hz0 : Filter.Tendsto
      (fun m => Fn (φ m) (zn (φ m) + (k : ℂ) * (T : ℂ) * Complex.I)) Filter.atTop (𝓝 0) := by
    have hzero : ∀ m, Fn (φ m) (zn (φ m) + (k : ℂ) * (T : ℂ) * Complex.I) = 0 := by
      intro m
      have hTeq : Tn (φ m) = T := hφspec m
      have h := hper (φ m) k
      rw [hTeq] at h
      exact h
    simp only [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hcomp hz0

/-- The clock-escape statement: an aperiodic zero admits no approximation by progression-riding
zeros of a locally uniform approximating family whose periods come from a fixed finite inventory.

If `F` has an aperiodic zero at `z` — a zero on no full vertical progression of `F`-zeros — and
`Fₙ → F` locally uniformly on a shift-closed `Ω` with all inventory periods positive, then there is
no sequence of `Fₙ`-zeros `zₙ → z` each riding a two-sided vertical progression of `Fₙ`-zeros of
period `Tₙ ∈ 𝒯`. The clock responsible for `z` escapes every finite period inventory. For an Euler
product this forces the responsible prime — whose column contributes period `2π/log p` — to leave
every finite set.

Mechanism: any such approximating data feeds `periodic_zero_limit`, producing a positive period
`T ∈ 𝒯` on whose vertical progression `z` sits, contradicting aperiodicity of the zero at `z`. -/
theorem aperiodic_zero_clock_escape {Ω : Set ℂ}
    (hΩshift : ∀ w ∈ Ω, ∀ t : ℝ, w + (t : ℂ) * Complex.I ∈ Ω)
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ} {𝒯 : Finset ℝ}
    (hconv : TendstoLocallyUniformlyOn Fn F Filter.atTop Ω)
    (hFc : ContinuousOn F Ω)
    {z : ℂ} (hz : z ∈ Ω) (haper : AperiodicZeroAt F z)
    (h𝒯pos : ∀ T ∈ 𝒯, 0 < T) :
    ¬ ∃ (zn : ℕ → ℂ) (Tn : ℕ → ℝ),
      Filter.Tendsto zn Filter.atTop (nhds z) ∧ (∀ n, zn n ∈ Ω)
        ∧ (∀ n, Tn n ∈ 𝒯) ∧ ∀ n, ∀ k : ℤ, Fn n (zn n + (k * Tn n) * Complex.I) = 0 := by
  rintro ⟨zn, Tn, hzn, hznΩ, hTn, hper⟩
  obtain ⟨T, hT, hprog⟩ := periodic_zero_limit hΩshift hconv hFc hz hzn hznΩ hTn hper
  exact haper.2 ⟨T, h𝒯pos T hT, hprog⟩

end RHTower
