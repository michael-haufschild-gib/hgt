/-
# Symmetry alone does not force the charge: the softness counterexample

The deck charge of an FE- and Schwarz-symmetric carrier is `V₄`-invariant
(`carrierCharge_quadruple`).  Does that symmetry *force* the charge to be trivial off the
critical line?  It does not.  This file exhibits an explicit entire carrier that has both
symmetries and yet carries an odd (nontrivial) charge at an off-line point:

  `f(s) = (s − ρ₀)(s − (1−ρ₀))(s − ρ̄₀)(s − (1−ρ̄₀))`,

the quartic on the full `V₄` orbit of an off-line `ρ₀`.  For `ρ₀` off the critical line and
off the real axis the four orbit points are distinct, so `ρ₀` is a *simple* zero and
`carrierCharge f 1 ρ₀ = (−1)¹ = −1`.

The consequence is sharp: the functional equation and Schwarz reflection are a genuine
constraint on the charge — they pin it to a `V₄`-invariant — but they are **not** the
constraint that trivializes it off the seam.  A second, non-symmetry input is required.
This is the softness end of the Goldilocks trichotomy, made explicit on the charge itself:
the class of FE-symmetric carriers is too soft to force `carrierCharge = 1` off the line.

The witness is an explicit polynomial exhibited to refute a would-be implication; no carrier
is grown by any flow.

The positive side of the boundary is `carrierCharge_one_eq_one_of_reflection`: a carrier with
a *holomorphic reflection about ρ* (`f(2ρ − s) = f(s)`) has even order at ρ, so its charge
there is `1`.  The only entire involution fixing ρ is that reflection, so this is the operative
forcing.  For ξ the functional equation is the reflection about `½`, so `carrierCharge ξ 1 ½ = 1`
(`carrierCharge_xi_central`) — but ξ has no reflection about an off-line point, which is exactly
why the first rung is open there.  Positive (reflection forces) and negative (symmetry-without-a-
fixed-point does not) bracket the Goldilocks middle: the forcing input is a symmetry that *fixes*
the point, and ξ has it only on the seam.
-/
import GaloisForLFunctions.RHTower.CarrierDeckCharge
import GaloisForLFunctions.RHTower.ReflectionParity
import GaloisForLFunctions.RHTower.EntireAutomorphism

namespace RHTower

open Complex Filter Topology

/-! ## The positive lever: a reflection about ρ forces the charge -/

/-- **Reflection forces triviality.**  A carrier with a holomorphic reflection about `ρ`
(`f(2ρ − s) = f(s)`) has even vanishing order at `ρ`, so its level-`2` deck charge there is
`1`.  This is the positive Goldilocks input: a symmetry that *fixes* the point trivializes the
charge (the degenerate `f ≡ 0` case gives order `0`, charge `1`, as well). -/
theorem carrierCharge_one_eq_one_of_reflection {f : ℂ → ℂ} {ρ : ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hsym : ∀ s, f (2 * ρ - s) = f s) :
    carrierCharge f 1 ρ = 1 := by
  rw [carrierCharge_one_eq_neg_one_pow]
  by_cases hne : analyticOrderAt f ρ = ⊤
  · rw [hne]; simp
  · exact (analyticOrderAt_even_of_reflection hf hsym hne).neg_one_pow

/-- **ξ's charge is forced at the centre.**  The functional equation is the reflection about
`½`, so ξ has even order there and `carrierCharge ξ 1 ½ = 1`: the one point ξ's own symmetry
forces.  Off the critical line ξ has no reflection about the point, and the charge is unforced
by symmetry — the open content of the first rung. -/
theorem carrierCharge_xi_central : carrierCharge xi 1 (1 / 2 : ℂ) = 1 := by
  refine carrierCharge_one_eq_one_of_reflection xi_analyticOnNhd_univ (fun s => ?_)
  have h : (2 * (1 / 2 : ℂ) - s) = 1 - s := by ring
  rw [h, xi_one_sub]

/-- **Rotational symmetry forces divisibility.**  If a carrier `f` is invariant under the
order-`n` rotation `s ↦ ρ + ζ(s − ρ)` about `ρ`, with `ζ` a primitive `n`-th root of unity,
then `n` divides the vanishing order of `f` at `ρ`.  The reflection lever is the case `n = 2`,
`ζ = −1`; a primitive `2^k`-rotation forces the full `2^k`-divisibility, i.e. the `k`-th rung
at that point.  The proof is the peel-and-continuity argument at the fixed point: the peel
cofactor `h` satisfies `h(s) = ζ^{ord}·h(ρ + ζ(s − ρ))`, and at `s → ρ` this forces `ζ^{ord} = 1`,
so `n ∣ ord`. -/
theorem analyticOrderAt_dvd_of_rotation {f : ℂ → ℂ} {ρ ζ : ℂ} {n : ℕ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hζ : IsPrimitiveRoot ζ n)
    (hsym : ∀ s, f (ρ + ζ * (s - ρ)) = f s)
    (hne : analyticOrderAt f ρ ≠ ⊤) :
    (n : ℕ∞) ∣ analyticOrderAt f ρ := by
  set m : ℕ := (analyticOrderAt f ρ).toNat with hm_def
  have hcoe : analyticOrderAt f ρ = (m : ℕ∞) := (ENat.coe_toNat hne).symm
  obtain ⟨h, hhan, hh0, hfact, -⟩ := exists_peel isOpen_univ hf (Set.mem_univ ρ) hcoe
  have key : ∀ᶠ s in 𝓝[≠] ρ, h s = ζ ^ m * h (ρ + ζ * (s - ρ)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : s ≠ ρ := hs
    have e1 : f s = (s - ρ) ^ m * h s := hfact s (Set.mem_univ s)
    have e2 : f (ρ + ζ * (s - ρ)) = (ρ + ζ * (s - ρ) - ρ) ^ m * h (ρ + ζ * (s - ρ)) :=
      hfact _ (Set.mem_univ _)
    have e3 : (ρ + ζ * (s - ρ) - ρ : ℂ) = ζ * (s - ρ) := by ring
    have e4 : f (ρ + ζ * (s - ρ)) = f s := hsym s
    have hpow : ((s - ρ : ℂ)) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hs')
    have e5 : (s - ρ) ^ m * h s = (s - ρ) ^ m * (ζ ^ m * h (ρ + ζ * (s - ρ))) := by
      rw [← e1, ← e4, e2, e3, mul_pow]; ring
    exact mul_left_cancel₀ hpow e5
  have hcont1 : Tendsto h (𝓝[≠] ρ) (𝓝 (h ρ)) :=
    ((hhan ρ (Set.mem_univ ρ)).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hrot : Tendsto (fun s : ℂ => ρ + ζ * (s - ρ)) (𝓝 ρ) (𝓝 ρ) := by
    have hc : Continuous (fun s : ℂ => ρ + ζ * (s - ρ)) := by fun_prop
    have := hc.tendsto ρ
    simpa using this
  have hcont2 : Tendsto (fun s : ℂ => ζ ^ m * h (ρ + ζ * (s - ρ))) (𝓝[≠] ρ)
      (𝓝 (ζ ^ m * h ρ)) := by
    have hcomp : Tendsto (fun s : ℂ => h (ρ + ζ * (s - ρ))) (𝓝 ρ) (𝓝 (h ρ)) :=
      ((hhan ρ (Set.mem_univ ρ)).continuousAt.tendsto).comp hrot
    exact (hcomp.const_mul _).mono_left nhdsWithin_le_nhds
  have heq : h ρ = ζ ^ m * h ρ := tendsto_nhds_unique (hcont1.congr' key) hcont2
  have hζm : ζ ^ m = 1 := by
    have h1 : ζ ^ m * h ρ = 1 * h ρ := by rw [one_mul, ← heq]
    exact mul_right_cancel₀ hh0 h1
  rw [hcoe]
  exact_mod_cast Nat.cast_dvd_cast ((hζ.pow_eq_one_iff_dvd m).mp hζm)

/-- **Rotational symmetry forces the charge.**  A carrier invariant under a primitive
`2^k`-rotation about `ρ` has `2^k ∣ ord_ρ(f)`, so `carrierCharge f k ρ = 1`: the general
positive Goldilocks lever, forcing the whole `k`-th rung at the fixed point of the rotation. -/
theorem carrierCharge_eq_one_of_rotation {f : ℂ → ℂ} {ρ ζ : ℂ} {k : ℕ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hsym : ∀ s, f (ρ + ζ * (s - ρ)) = f s) :
    carrierCharge f k ρ = 1 := by
  rw [carrierCharge_eq_one_iff_dvd]
  by_cases hne : analyticOrderAt f ρ = ⊤
  · rw [ENat.toNat_eq_zero.mpr (Or.inr hne)]; exact dvd_zero _
  · have hd := analyticOrderAt_dvd_of_rotation hf hζ hsym hne
    have hcoe : analyticOrderAt f ρ = (((analyticOrderAt f ρ).toNat : ℕ) : ℕ∞) :=
      (ENat.coe_toNat hne).symm
    rw [hcoe] at hd
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) hd

/-- The `V₄`-orbit quartic of a point `ρ₀`: an entire carrier with zeros exactly at
`{ρ₀, 1−ρ₀, ρ̄₀, 1−ρ̄₀}`. -/
noncomputable def orbitQuartic (ρ₀ : ℂ) : ℂ → ℂ :=
  fun s => (s - ρ₀) * ((s - (1 - ρ₀)) * (s - (starRingEnd ℂ) ρ₀) *
    (s - (1 - (starRingEnd ℂ) ρ₀)))

theorem orbitQuartic_differentiable (ρ₀ : ℂ) : Differentiable ℂ (orbitQuartic ρ₀) := by
  unfold orbitQuartic; fun_prop

/-- The quartic satisfies the functional equation `f(1−s) = f(s)`: its zero set is
`1 − ·`-invariant. -/
theorem orbitQuartic_fe (ρ₀ : ℂ) (s : ℂ) :
    orbitQuartic ρ₀ (1 - s) = orbitQuartic ρ₀ s := by
  unfold orbitQuartic; ring

/-- The quartic is Schwarz-equivariant `f(s̄) = \overline{f(s)}`: its zero set is
conjugation-invariant. -/
theorem orbitQuartic_conj (ρ₀ : ℂ) (s : ℂ) :
    orbitQuartic ρ₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (orbitQuartic ρ₀ s) := by
  unfold orbitQuartic
  simp only [map_mul, map_sub, map_one, Complex.conj_conj]
  ring

/-- At an off-line, off-real point the three non-`ρ₀` orbit factors are nonzero at `ρ₀`. -/
theorem orbitQuartic_cofactor_ne_zero {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) :
    (ρ₀ - (1 - ρ₀)) * (ρ₀ - (starRingEnd ℂ) ρ₀) * (ρ₀ - (1 - (starRingEnd ℂ) ρ₀)) ≠ 0 := by
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · -- ρ₀ − (1 − ρ₀) = 2ρ₀ − 1, real part 2ρ₀.re − 1 ≠ 0
    intro h
    apply hre
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hr
    linarith
  · -- ρ₀ − ρ̄₀ = 2i·Im ρ₀, imaginary part 2 Im ρ₀ ≠ 0
    intro h
    apply him
    have hi := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at hi
    linarith
  · -- ρ₀ − (1 − ρ̄₀) = 2 Re ρ₀ − 1 (real), real part ≠ 0
    intro h
    apply hre
    have hr := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re, Complex.zero_re] at hr
    linarith

/-- At an off-line, off-real point `ρ₀` the quartic has a **simple** zero. -/
theorem orbitQuartic_order_one {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) :
    analyticOrderAt (orbitQuartic ρ₀) ρ₀ = 1 := by
  set g : ℂ → ℂ := fun s => (s - (1 - ρ₀)) * (s - (starRingEnd ℂ) ρ₀) *
    (s - (1 - (starRingEnd ℂ) ρ₀)) with hg
  have hfeq : orbitQuartic ρ₀ = (fun s => s - ρ₀) * g := by
    funext s; simp only [orbitQuartic, hg, Pi.mul_apply]
  have hlin_an : AnalyticAt ℂ (fun s : ℂ => s - ρ₀) ρ₀ := analyticAt_id.sub analyticAt_const
  have hg_an : AnalyticAt ℂ g ρ₀ := by rw [hg]; fun_prop
  have hg0 : g ρ₀ ≠ 0 := orbitQuartic_cofactor_ne_zero hre him
  have hord_lin : analyticOrderAt (fun s : ℂ => s - ρ₀) ρ₀ = 1 := by
    refine hlin_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
    · simp
    · have : deriv (fun s : ℂ => s - ρ₀) ρ₀ = 1 :=
        ((hasDerivAt_id ρ₀).sub_const ρ₀).deriv
      rw [this]; exact one_ne_zero
  have hord_g : analyticOrderAt g ρ₀ = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hg0)
  rw [hfeq, analyticOrderAt_mul hlin_an hg_an, hord_lin, hord_g, add_zero]

/-- **Softness: symmetry does not force the charge.**  For every `ρ₀` off the critical line
and off the real axis there is an entire carrier `f` with the functional equation and Schwarz
reflection whose level-`2` deck charge at `ρ₀` is `−1` — the charge is nontrivial off the
seam.  Hence FE-symmetry alone cannot force `carrierCharge f 1 = 1` off the line: a second,
non-symmetry input is needed. -/
theorem exists_feSchwarz_carrier_odd_charge {ρ₀ : ℂ} (hre : ρ₀.re ≠ 1 / 2) (him : ρ₀.im ≠ 0) :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧
      (∀ s, f (1 - s) = f s) ∧
      (∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s)) ∧
      carrierCharge f 1 ρ₀ = -1 := by
  refine ⟨orbitQuartic ρ₀, orbitQuartic_differentiable ρ₀, orbitQuartic_fe ρ₀,
    orbitQuartic_conj ρ₀, ?_⟩
  rw [carrierCharge_one_eq_neg_one_pow, orbitQuartic_order_one hre him]
  simp

/-- **Uniqueness of the symmetric forcing, applied to the charge.**  If a carrier `f` is
invariant under an entire finite-order symmetry `φ` fixing `ρ` (`φ^[2^k] = id`) whose rotation
multiplier is a primitive `2^k`-th root of unity, then `carrierCharge f k ρ = 1`.  The
classification `finiteOrder_entire_fixing_is_rotation` supplies that `φ` is a rotation, and the
rotation lever forces the rung: the rotation is the *only* symmetric forcing there can be. -/
theorem carrierCharge_eq_one_of_finiteOrder_symmetry {f φ : ℂ → ℂ} {ρ : ℂ} {k : ℕ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hφ : Differentiable ℂ φ)
    (hord : φ^[2 ^ k] = id) (hfix : φ ρ = ρ) (hinv : ∀ s, f (φ s) = f s)
    (hprim : ∀ a : ℂ, a ^ (2 ^ k) = 1 → (∀ z, φ z = ρ + a * (z - ρ)) → IsPrimitiveRoot a (2 ^ k)) :
    carrierCharge f k ρ = 1 := by
  obtain ⟨a, han, hrot⟩ :=
    finiteOrder_entire_fixing_is_rotation hφ (pow_pos (by norm_num) k) hord hfix
  refine carrierCharge_eq_one_of_rotation hf (hprim a han hrot) (fun s => ?_)
  rw [← hrot s]; exact hinv s

end RHTower
