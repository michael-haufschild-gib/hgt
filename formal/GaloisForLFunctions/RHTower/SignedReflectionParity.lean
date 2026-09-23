/-
The signed reflection-parity law: the sign of the functional equation fixes the parity of the
central order.

`analyticOrderAt_even_of_reflection` handles the symmetric case `f(2c − s) = f(s)` (even order at the
fixed point).  The complete statement carries the sign: for `f(2c − s) = ε·f(s)` with `ε = ±1`, the
peel `f = (s − c)^m·h` reflects to `(−1)^m·h(2c − s) = ε·h(s)`, and evaluating at the fixed point
(`h(c) ≠ 0`) forces

  `(−1)^m = ε`   (`neg_one_pow_orderAt_of_signed_reflection`).

Thus the parity of the vanishing order at the reflection's fixed point is determined entirely by the
reflection sign: `ε = +1` gives even order (the symmetric case), and the antisymmetric case `ε = −1`
forces ODD order — a forced simple/odd central zero (`analyticOrderAt_odd_of_antireflection`).

This is the fixed-point half of the parity picture: the sign is a datum of the *fixed point*.  Away
from the fixed point a reflection about `c` moves the point, so there is no sign to read and no order
constraint — the reason the central mechanism does not reach off-fixed zeros
(`exists_feSchwarz_carrier_odd_charge` exhibits an FE-symmetric carrier with an odd off-fixed charge).
-/
import GaloisForLFunctions.RHTower.ReflectionParity

open Complex Filter Topology

namespace RHTower

/-- **Antisymmetric reflection forces odd order at the fixed point.**  If `f` is analytic on `ℂ` and
antisymmetric under `s ↦ 2c − s` (`f(2c − s) = −f(s)`), with finite order at the fixed point `c`, that
order is odd: the sign `ε = −1` of the functional equation forces an odd (in particular nonzero)
central vanishing.  This is the mirror of `analyticOrderAt_even_of_reflection` at the opposite sign. -/
theorem analyticOrderAt_odd_of_antireflection {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hsym : ∀ s, f (2 * c - s) = - f s)
    (hne : analyticOrderAt f c ≠ ⊤) :
    Odd (analyticOrderAt f c).toNat := by
  have h := neg_one_pow_orderAt_of_signed_reflection hf (Or.inr rfl)
    (fun s => by rw [hsym s]; ring) hne
  rcases Nat.even_or_odd (analyticOrderAt f c).toNat with he | ho
  · rw [he.neg_one_pow] at h; norm_num at h
  · exact ho

/-- **Antisymmetric reflection forces odd order, germ form.**  A germ antisymmetric under
`s ↦ 2c − s` (`f(2c − s) = −f(s)` near `c`) has odd order at `c`. -/
theorem analyticOrderAt_odd_of_antireflection_eventually {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hsym : ∀ᶠ s in 𝓝 c, f (2 * c - s) = - f s)
    (hne : analyticOrderAt f c ≠ ⊤) :
    Odd (analyticOrderAt f c).toNat := by
  have h := neg_one_pow_orderAt_of_signed_reflection_eventually hf (Or.inr rfl)
    (hsym.mono fun s hs => by rw [hs]; ring) hne
  rcases Nat.even_or_odd (analyticOrderAt f c).toNat with he | ho
  · rw [he.neg_one_pow] at h; norm_num at h
  · exact ho

/-! ### The derivative tower: central parity alternates under differentiation -/

/-- **Differentiation flips the reflection sign.**  Under the reflection `s ↦ 2c − s`, the derivative
of a sign-symmetric function is sign-symmetric with the opposite sign: `f(2c − s) = ε·f(s)` gives
`f′(2c − s) = −ε·f′(s)` (the chain-rule factor `−1` from the reflection). -/
theorem deriv_signed_reflection {f : ℂ → ℂ} {c ε : ℂ}
    (hf : Differentiable ℂ f) (hsym : ∀ s, f (2 * c - s) = ε * f s) :
    ∀ s, deriv f (2 * c - s) = -ε * deriv f s := by
  intro s
  have hg : HasDerivAt (fun s : ℂ => 2 * c - s) (-1) s := by
    simpa using! (hasDerivAt_const s (2 * c)).sub (hasDerivAt_id s)
  have hcomp : HasDerivAt (fun s => f (2 * c - s)) (deriv f (2 * c - s) * (-1)) s :=
    (hf (2 * c - s)).hasDerivAt.comp s hg
  have heqfun : (fun s => f (2 * c - s)) = (fun s => ε * f s) := funext hsym
  rw [heqfun] at hcomp
  have hrhs : HasDerivAt (fun s => ε * f s) (ε * deriv f s) s :=
    ((hf s).hasDerivAt).const_mul ε
  have huniq := hcomp.unique hrhs
  linear_combination -huniq

/-- Every iterated derivative of an entire function is entire. -/
theorem iteratedDeriv_analyticOnNhd_univ {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    ∀ n, AnalyticOnNhd ℂ (deriv^[n] f) Set.univ
  | 0 => by simpa using hf
  | (n + 1) => by
      rw [Function.iterate_succ']
      exact AnalyticOnNhd.deriv (iteratedDeriv_analyticOnNhd_univ hf n)

/-- **Differentiation `n` times multiplies the reflection sign by `(−1)^n`.**  Iterating
`deriv_signed_reflection`: `f(2c − s) = ε·f(s)` gives `(deriv^n f)(2c − s) = (−1)^n·ε·(deriv^n f)(s)`. -/
theorem iteratedDeriv_signed_reflection {f : ℂ → ℂ} {c ε : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hsym : ∀ s, f (2 * c - s) = ε * f s) :
    ∀ n s, (deriv^[n] f) (2 * c - s) = (-1) ^ n * ε * (deriv^[n] f) s := by
  intro n
  induction n with
  | zero => intro s; simpa using hsym s
  | succ k ih =>
    have hdiffk : Differentiable ℂ (deriv^[k] f) :=
      fun z => (iteratedDeriv_analyticOnNhd_univ hf k z (Set.mem_univ z)).differentiableAt
    have hstep := deriv_signed_reflection (ε := (-1) ^ k * ε) hdiffk ih
    intro s
    have e1 : (deriv^[k + 1] f) (2 * c - s) = deriv (deriv^[k] f) (2 * c - s) := by
      rw [Function.iterate_succ']; rfl
    have e2 : (deriv^[k + 1] f) s = deriv (deriv^[k] f) s := by
      rw [Function.iterate_succ']; rfl
    rw [e1, e2, hstep s]; ring

/-- **Central parity through the derivative tower.**  If `f(2c − s) = ε·f(s)` (`ε = ±1`), the `n`-th
derivative's central order has reflection sign `(−1)^n·ε`: `(−1)^{ord_c (deriv^n f)} = (−1)^n·ε`.  The
whole derivative tower's central parity is fixed by the base sign, alternating with each
differentiation — even ↔ odd order swap at every step. -/
theorem neg_one_pow_orderAt_iteratedDeriv_of_signed_reflection {f : ℂ → ℂ} {c ε : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hε : ε = 1 ∨ ε = -1)
    (hsym : ∀ s, f (2 * c - s) = ε * f s) (n : ℕ)
    (hne : analyticOrderAt (deriv^[n] f) c ≠ ⊤) :
    (-1 : ℂ) ^ (analyticOrderAt (deriv^[n] f) c).toNat = (-1) ^ n * ε := by
  have hsign : ((-1 : ℂ) ^ n * ε) = 1 ∨ ((-1 : ℂ) ^ n * ε) = -1 := by
    rcases Nat.even_or_odd n with hn | hn
    · rw [hn.neg_one_pow, one_mul]; exact hε
    · rw [hn.neg_one_pow]; rcases hε with h | h <;> rw [h] <;> norm_num
  exact neg_one_pow_orderAt_of_signed_reflection (iteratedDeriv_analyticOnNhd_univ hf n) hsign
    (iteratedDeriv_signed_reflection hf hsym n) hne

/-- **A symmetric carrier's derivative has odd central order.**  `f(2c − s) = f(s)` ⟹ `f′` has odd
order at the fixed point `c` (the `n = 1` rung: the derivative is antisymmetric, so its central zero
is forced simple/odd).  The canonical instance is an even carrier's critical point at the seam. -/
theorem analyticOrderAt_deriv_odd_of_symmetric {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hsym : ∀ s, f (2 * c - s) = f s)
    (hne : analyticOrderAt (deriv f) c ≠ ⊤) :
    Odd (analyticOrderAt (deriv f) c).toNat := by
  have h := neg_one_pow_orderAt_iteratedDeriv_of_signed_reflection hf (Or.inl rfl)
    (fun s => by rw [hsym s]; ring) 1 (by simpa using hne)
  simp only [pow_one, Function.iterate_one] at h
  rcases Nat.even_or_odd (analyticOrderAt (deriv f) c).toNat with he | ho
  · rw [he.neg_one_pow] at h; norm_num at h
  · exact ho

/-! ### Taylor-coefficient evenness at the fixed point -/

/-- **A symmetric carrier has an even Taylor expansion at the fixed point.**  If `f(2c − s) = f(s)`,
every odd-index Taylor coefficient at `c` vanishes: `(deriv^n f)(c) = 0` for odd `n`.  This is the
"local coordinates force evenness of the transverse Taylor expansion" statement, proved by evaluating
the derivative-tower symmetry at the fixed point: `(deriv^n f)(c) = (−1)^n·(deriv^n f)(c)`, so an odd
`n` forces the coefficient to be its own negative.  (No finiteness of order is needed.) -/
theorem iteratedDeriv_odd_eq_zero_of_symmetric {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hsym : ∀ s, f (2 * c - s) = f s)
    {n : ℕ} (hn : Odd n) :
    (deriv^[n] f) c = 0 := by
  have h := iteratedDeriv_signed_reflection (ε := 1) hf (fun s => by rw [hsym s]; ring) n c
  rw [show 2 * c - c = c by ring, hn.neg_one_pow] at h
  linear_combination (1 / 2 : ℂ) * h

/-- **An antisymmetric carrier has an odd Taylor expansion at the fixed point.**  If
`f(2c − s) = −f(s)`, every even-index Taylor coefficient at `c` vanishes: `(deriv^n f)(c) = 0` for even
`n` — in particular `f(c) = 0` (the `n = 0` case), the forced central zero of the antisymmetric case. -/
theorem iteratedDeriv_even_eq_zero_of_antisymmetric {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hsym : ∀ s, f (2 * c - s) = - f s)
    {n : ℕ} (hn : Even n) :
    (deriv^[n] f) c = 0 := by
  have h := iteratedDeriv_signed_reflection (ε := -1) hf (fun s => by rw [hsym s]; ring) n c
  rw [show 2 * c - c = c by ring, hn.neg_one_pow] at h
  linear_combination (1 / 2 : ℂ) * h

/-! ### The exact reach of the forcing: the fixed point and not one point further -/

/-- The reflection-orbit pair of `ρ` about `c`: `(s − ρ)(s − (2c − ρ))`, symmetric about `c` with a
simple zero at `ρ`.  The minimal symmetric witness for the off-fixed freedom. -/
noncomputable def reflPair (c ρ : ℂ) : ℂ → ℂ := fun s => (s - ρ) * (s - (2 * c - ρ))

theorem reflPair_analytic (c ρ : ℂ) : AnalyticOnNhd ℂ (reflPair c ρ) Set.univ :=
  fun _ _ => (analyticAt_id.sub analyticAt_const).mul (analyticAt_id.sub analyticAt_const)

theorem reflPair_sym (c ρ : ℂ) (s : ℂ) : reflPair c ρ (2 * c - s) = reflPair c ρ s := by
  unfold reflPair; ring

theorem reflPair_order_one {c ρ : ℂ} (h : ρ ≠ c) : analyticOrderAt (reflPair c ρ) ρ = 1 := by
  have hlin_an : AnalyticAt ℂ (fun s : ℂ => s - ρ) ρ := analyticAt_id.sub analyticAt_const
  have hg_an : AnalyticAt ℂ (fun s : ℂ => s - (2 * c - ρ)) ρ := analyticAt_id.sub analyticAt_const
  have hg0 : (fun s : ℂ => s - (2 * c - ρ)) ρ ≠ 0 := by
    simp only
    intro hc
    apply h
    have h2 : ρ - c = 0 := by linear_combination hc / 2
    linear_combination h2
  have hord_lin : analyticOrderAt (fun s : ℂ => s - ρ) ρ = 1 := by
    refine hlin_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
    · simp
    · have : deriv (fun s : ℂ => s - ρ) ρ = 1 := ((hasDerivAt_id ρ).sub_const ρ).deriv
      rw [this]; exact one_ne_zero
  have hord_g : analyticOrderAt (fun s : ℂ => s - (2 * c - ρ)) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hg0)
  have hfeq : reflPair c ρ = (fun s : ℂ => s - ρ) * (fun s : ℂ => s - (2 * c - ρ)) := by
    funext s; simp only [reflPair, Pi.mul_apply]
  rw [hfeq, analyticOrderAt_mul hlin_an hg_an, hord_lin, hord_g, add_zero]

/-- **The exact reach of central parity.**  For the reflection `s ↦ 2c − s`, the property "every
entire reflection-symmetric carrier has even order at `ρ`" holds *precisely* at the fixed point
`ρ = c`.  At the fixed point it is `analyticOrderAt_even_of_reflection`; off the fixed point the
symmetric pair `(s − ρ)(s − (2c − ρ))` has a simple (odd) zero at `ρ`, so the forcing reaches exactly
the singleton fixed locus and not one point further.  This is the precise sense in which central
parity does not reach off-fixed zeros — for ξ the fixed point is `1/2`, so the functional equation
forces central parity only at the seam centre and nowhere off it. -/
theorem reflection_forces_even_iff_fixedPoint {c ρ : ℂ} :
    (∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f Set.univ → (∀ s, f (2 * c - s) = f s) →
       analyticOrderAt f ρ ≠ ⊤ → Even (analyticOrderAt f ρ).toNat)
    ↔ ρ = c := by
  constructor
  · intro hforce
    by_contra hne
    have hEven := hforce (reflPair c ρ) (reflPair_analytic c ρ) (reflPair_sym c ρ)
      (by rw [reflPair_order_one hne]; exact ENat.coe_ne_top 1)
    rw [reflPair_order_one hne] at hEven
    simp at hEven
  · rintro rfl
    intro f hf hsym hne
    exact analyticOrderAt_even_of_reflection hf hsym hne

/-- The antisymmetric witness of `ρ` about `c`: `(s − c)·((s − ρ)(s − (2c − ρ)))²`, antisymmetric
about `c` with an even (order-2) zero at `ρ`. -/
noncomputable def antiPair (c ρ : ℂ) : ℂ → ℂ := fun s => (s - c) * (reflPair c ρ s) ^ (2 : ℕ)

theorem antiPair_analytic (c ρ : ℂ) : AnalyticOnNhd ℂ (antiPair c ρ) Set.univ :=
  fun z _ => (analyticAt_id.sub analyticAt_const).mul
    ((reflPair_analytic c ρ z (Set.mem_univ z)).pow 2)

theorem antiPair_antisym (c ρ : ℂ) (s : ℂ) : antiPair c ρ (2 * c - s) = - antiPair c ρ s := by
  simp only [antiPair, reflPair_sym]; ring

theorem antiPair_order_two {c ρ : ℂ} (h : ρ ≠ c) : analyticOrderAt (antiPair c ρ) ρ = 2 := by
  have hlin_an : AnalyticAt ℂ (fun s : ℂ => s - c) ρ := analyticAt_id.sub analyticAt_const
  have hsq_an : AnalyticAt ℂ (fun s : ℂ => (reflPair c ρ s) ^ (2 : ℕ)) ρ :=
    (reflPair_analytic c ρ ρ (Set.mem_univ ρ)).pow 2
  have hlin0 : (fun s : ℂ => s - c) ρ ≠ 0 := by simp only; exact sub_ne_zero.mpr h
  have hord_lin : analyticOrderAt (fun s : ℂ => s - c) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hlin0)
  have hord_sq : analyticOrderAt (fun s : ℂ => (reflPair c ρ s) ^ (2 : ℕ)) ρ = 2 := by
    have hrp : (fun s : ℂ => (reflPair c ρ s) ^ (2 : ℕ)) = (reflPair c ρ) * (reflPair c ρ) := by
      funext s; simp [sq, Pi.mul_apply]
    rw [hrp, analyticOrderAt_mul (reflPair_analytic c ρ ρ (Set.mem_univ ρ))
      (reflPair_analytic c ρ ρ (Set.mem_univ ρ)), reflPair_order_one h]
    rfl
  have hfeq : antiPair c ρ = (fun s : ℂ => s - c) * (fun s : ℂ => (reflPair c ρ s) ^ (2 : ℕ)) := by
    funext s; simp only [antiPair, Pi.mul_apply]
  rw [hfeq, analyticOrderAt_mul hlin_an hsq_an, hord_lin, hord_sq, zero_add]

/-- **The exact reach of antisymmetric central parity.**  For `s ↦ 2c − s`, "every entire
antisymmetric carrier has odd order at `ρ`" holds precisely at the fixed point `ρ = c`.  Off the fixed
point `(s − c)·((s − ρ)(s − (2c − ρ)))²` is antisymmetric with an even (order-2) zero at `ρ` — so the
ε = −1 forcing, like the ε = +1 case, reaches exactly the singleton fixed locus. -/
theorem antireflection_forces_odd_iff_fixedPoint {c ρ : ℂ} :
    (∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f Set.univ → (∀ s, f (2 * c - s) = - f s) →
       analyticOrderAt f ρ ≠ ⊤ → Odd (analyticOrderAt f ρ).toNat)
    ↔ ρ = c := by
  constructor
  · intro hforce
    by_contra hne
    have hOdd := hforce (antiPair c ρ) (antiPair_analytic c ρ) (antiPair_antisym c ρ)
      (by rw [antiPair_order_two hne]; exact ENat.coe_ne_top 2)
    rw [antiPair_order_two hne] at hOdd
    exact absurd hOdd (by decide)
  · rintro rfl
    intro f hf hsym hne
    exact analyticOrderAt_odd_of_antireflection hf hsym hne

/-! ### The even descent: the Taylor evenness packaged as a factorization through squaring -/

/-- **An even entire function descends through squaring.**  If `Y` is entire and even
(`Y(−z) = Y(z)`), there is an entire `X` with `Y(z) = X(z²)` for all `z`.  This is the packaged form
of the transverse-Taylor evenness (`iteratedDeriv_odd_eq_zero_of_symmetric`): the odd coefficients
vanish, so `Y` is a function of `z²`.  Construction: `X(u) := Y(√u)` for a chosen root (well-defined
by evenness); it is analytic off `0` because `X ∘ (·²) = Y` and `z ↦ z²` has nonzero derivative there
(`analyticAt_comp_iff_of_deriv_ne_zero`), and analytic at `0` by removable singularity (`X` is bounded
there since `‖√u‖ = √‖u‖ → 0`). -/
theorem even_descent {Y : ℂ → ℂ} (hY : AnalyticOnNhd ℂ Y Set.univ) (hev : ∀ z, Y (-z) = Y z) :
    ∃ X : ℂ → ℂ, AnalyticOnNhd ℂ X Set.univ ∧ ∀ z, Y z = X (z ^ (2 : ℕ)) := by
  classical
  set rt : ℂ → ℂ := fun u => (IsAlgClosed.exists_pow_nat_eq u (n := 2) two_pos).choose with hrt
  have hrt2 : ∀ u, (rt u) ^ (2 : ℕ) = u := fun u =>
    (IsAlgClosed.exists_pow_nat_eq u (n := 2) two_pos).choose_spec
  set X : ℂ → ℂ := fun u => Y (rt u) with hX
  have hYany : ∀ (u z : ℂ), z ^ (2 : ℕ) = u → Y z = X u := by
    intro u z hz
    have hsq : z ^ (2 : ℕ) = (rt u) ^ (2 : ℕ) := by rw [hz, hrt2]
    have hpm : z = rt u ∨ z = - rt u := by
      have h0 : (z - rt u) * (z + rt u) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp h0 with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (by linear_combination h)
    rcases hpm with h | h
    · rw [hX]; simp only; rw [h]
    · rw [hX]; simp only; rw [h, hev]
  have hXY : ∀ z, Y z = X (z ^ (2 : ℕ)) := fun z => hYany (z ^ (2 : ℕ)) z rfl
  have hcomp : (X ∘ fun z : ℂ => z ^ (2 : ℕ)) = Y := by
    funext z; simp only [Function.comp_apply]; exact (hXY z).symm
  have hXaway : ∀ u : ℂ, u ≠ 0 → AnalyticAt ℂ X u := by
    intro u hu
    have hz₀2 : (rt u) ^ (2 : ℕ) = u := hrt2 u
    have hz₀0 : rt u ≠ 0 := fun h => hu (by rw [← hz₀2, h]; ring)
    have hsqa : AnalyticAt ℂ (fun z : ℂ => z ^ (2 : ℕ)) (rt u) := analyticAt_id.pow 2
    have hd0 : deriv (fun z : ℂ => z ^ (2 : ℕ)) (rt u) ≠ 0 := by
      rw [(hasStrictDerivAt_pow 2 (rt u)).hasDerivAt.deriv]
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ hz₀0)
    have hYz₀ : AnalyticAt ℂ (X ∘ fun z : ℂ => z ^ (2 : ℕ)) (rt u) := by
      rw [hcomp]; exact hY (rt u) (Set.mem_univ _)
    have hres := (analyticAt_comp_iff_of_deriv_ne_zero hsqa hd0).mp hYz₀
    rwa [hz₀2] at hres
  have hrt0 : rt 0 = 0 := pow_eq_zero_iff (by norm_num) |>.mp (hrt2 0)
  have hX0 : X 0 = Y 0 := by rw [hX]; simp only; rw [hrt0]
  have hnorm : ∀ u, ‖rt u‖ = Real.sqrt ‖u‖ := fun u => by
    rw [← Real.sqrt_sq (norm_nonneg (rt u)), ← norm_pow, hrt2]
  have hrt_tendsto : Tendsto rt (𝓝 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    rw [show (fun u => ‖rt u‖) = fun u => Real.sqrt ‖u‖ from funext hnorm]
    simpa using! (Real.continuous_sqrt.comp continuous_norm).tendsto (0 : ℂ)
  have hcont0 : ContinuousAt X 0 := by
    have hcomp0 : Tendsto (fun u => Y (rt u)) (𝓝 0) (𝓝 (Y 0)) :=
      (hY 0 (Set.mem_univ 0)).continuousAt.tendsto.comp hrt_tendsto
    rw [ContinuousAt, hX0]; exact hcomp0
  have hX0an : AnalyticAt ℂ X 0 := by
    refine analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ hcont0
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact (hXaway u hu).differentiableAt
  refine ⟨X, fun u _ => ?_, hXY⟩
  rcases eq_or_ne u 0 with rfl | hu
  · exact hX0an
  · exact hXaway u hu

/-- **The FE-symmetric descent.**  An entire carrier symmetric about `c` (`f(2c − s) = f(s)`) factors
through the transverse square: there is an entire `X` with `f(s) = X((s − c)²)` for all `s`.  The
functional equation becomes single-valued evenness in the `u = (s − c)²` coordinate.  (For ξ about
`1/2` this is the banked `xi_eq_xiDescent`; here it is the general statement for any symmetric pencil
member.) -/
theorem symmetric_descent {f : ℂ → ℂ} {c : ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hsym : ∀ s, f (2 * c - s) = f s) :
    ∃ X : ℂ → ℂ, AnalyticOnNhd ℂ X Set.univ ∧ ∀ s, f s = X ((s - c) ^ (2 : ℕ)) := by
  set Y : ℂ → ℂ := fun z => f (c + z) with hYdef
  have hYan : AnalyticOnNhd ℂ Y Set.univ := fun z _ =>
    (hf (c + z) (Set.mem_univ _)).comp (analyticAt_const.add analyticAt_id)
  have hYev : ∀ z, Y (-z) = Y z := fun z => by
    simp only [hYdef]; rw [show c + -z = 2 * c - (c + z) by ring, hsym]
  obtain ⟨X, hX, hXY⟩ := even_descent hYan hYev
  refine ⟨X, hX, fun s => ?_⟩
  rw [show f s = Y (s - c) from by simp only [hYdef]; rw [show c + (s - c) = s by ring], hXY]

/-- **Uniqueness of the descent.**  Any two carriers agreeing after the square substitution agree
everywhere, since `s ↦ (s − c)²` is surjective: the descent `X` of `symmetric_descent` is unique. -/
theorem descent_unique {X₁ X₂ : ℂ → ℂ} {c : ℂ}
    (h : ∀ s, X₁ ((s - c) ^ (2 : ℕ)) = X₂ ((s - c) ^ (2 : ℕ))) : ∀ u, X₁ u = X₂ u := by
  intro u
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq u (n := 2) two_pos
  have hu := h (c + z)
  rw [show c + z - c = z by ring, hz] at hu
  exact hu

end RHTower
