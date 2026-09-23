import GaloisForLFunctions.HTGeometry.MeromorphicPrincipalPart
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import GaloisForLFunctions.HTGeometry.GammaDifferentialFE

/-!
# The residue of a meromorphic function against a Cauchy kernel

If `H` is meromorphic at `ρ` and `Z ≠ ρ`, then

`Res_{s = ρ} [ H(s)/(Z − s) ] = (principal part of `H` at `ρ`) evaluated at `Z`.`

This is the exact form of Burnol's remark in Theorem 5.2 that "the contribution of `ρ` is a linear
combination of `ζ(Z)/(Z − ρ)^l`, `1 ≤ l ≤ m_ρ`": the residue at a zero of `ζ` of multiplicity `m` is
a linear combination of `(Z − ρ)^{-l}`, `1 ≤ l ≤ m`, with coefficients the Laurent coefficients of
`H` at `ρ`.

## Main results

* `taylorCoeffZero_inv_sub` — the geometric Taylor coefficients of the Cauchy kernel.
* `laurentCoeff_inv_pow_mul_inv_sub`
* `laurentCoeff_mul_inv_sub` — **the residue is the principal part evaluated at `Z`.**
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The Cauchy kernel at the origin -/

theorem taylorCoeffZero_inv_sub {w : ℂ} (hw : w ≠ 0) (j : ℕ) :
    taylorCoeffZero (fun t : ℂ => (w - t)⁻¹) j = (w⁻¹) ^ (j + 1) := by
  have hfun : (fun t : ℂ => (w - t)⁻¹) = fun t : ℂ => (-1 : ℂ) * (t + (-w))⁻¹ := by
    funext t
    have h : w - t = -(t + (-w)) := by ring
    rw [h, inv_neg]
    ring
  have hne : (0 : ℂ) + (-w) ≠ 0 := by simpa using hw
  have hderiv : iteratedDeriv j (fun t : ℂ => (w - t)⁻¹) 0
      = (-1 : ℂ) * ((-1) ^ j * (j.factorial : ℂ) * (((0 : ℂ) + (-w)) ^ (j + 1))⁻¹) := by
    rw [hfun, iteratedDeriv_const_mul_field, iteratedDeriv_inv_add_const (-w) j 0 hne]
  rw [taylorCoeffZero, hderiv]
  have hzero : ((0 : ℂ) + (-w)) ^ (j + 1) = (-1) ^ (j + 1) * w ^ (j + 1) := by
    rw [zero_add, neg_pow]
  rw [hzero, mul_inv, inv_pow]
  have hfac : ((j.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hsign : ((-1 : ℂ) ^ (j + 1))⁻¹ = (-1 : ℂ) ^ (j + 1) := by
    rcases Nat.even_or_odd (j + 1) with h | h
    · rw [h.neg_one_pow]
      norm_num
    · rw [h.neg_one_pow]
      norm_num
  rw [hsign]
  field_simp
  have hsq : ((-1 : ℂ) ^ j * (-1) ^ j) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have h2 : ((-1 : ℂ) ^ j * (-1) ^ (j + 1)) = -1 := by
    rw [pow_succ, ← mul_assoc, hsq]
    ring
  rw [h2]
  ring

/-! ## An inverse power against the kernel -/

theorem laurentCoeff_inv_pow_mul_inv_sub {ρ Z : ℂ} (hZ : Z ≠ ρ) {m : ℕ} (hm : 1 ≤ m) :
    laurentCoeff (fun s : ℂ => ((s - ρ) ^ m)⁻¹ * (Z - s)⁻¹) ρ (-1) = ((Z - ρ)⁻¹) ^ m := by
  set w : ℂ := Z - ρ with hwdef
  have hw : w ≠ 0 := sub_ne_zero.2 hZ
  set F : ℂ → ℂ := fun s : ℂ => ((s - ρ) ^ m)⁻¹ * (Z - s)⁻¹ with hFdef
  -- the clearing shift at exponent `m + 1`
  have hshift : laurentShift F ρ (m + 1) = fun t : ℂ => t * (w - t)⁻¹ := by
    funext t
    rw [laurentShift, hFdef]
    simp only
    have harg : (ρ + t - ρ) = t := by ring
    have harg2 : Z - (ρ + t) = w - t := by rw [hwdef]; ring
    rw [harg, harg2]
    rcases eq_or_ne t 0 with rfl | ht
    · simp [zero_pow (by omega : m ≠ 0)]
    · rw [pow_succ]
      field_simp
  have hana : AnalyticAt ℂ (laurentShift F ρ (m + 1)) 0 := by
    rw [hshift]
    have hker : AnalyticAt ℂ (fun t : ℂ => (w - t)⁻¹) 0 := by
      refine AnalyticAt.inv ?_ (by simpa using hw)
      fun_prop
    exact analyticAt_id.mul hker
  have hℓ : (0 : ℤ) ≤ (-1 : ℤ) + ((m + 1 : ℕ) : ℤ) := by
    have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    omega
  rw [laurentCoeff_eq_taylorCoeffZero hana hℓ, hshift]
  have hidx : ((-1 : ℤ) + ((m + 1 : ℕ) : ℤ)).toNat = m := by
    push_cast
    omega
  rw [hidx]
  have hker : AnalyticAt ℂ (fun t : ℂ => (w - t)⁻¹) 0 := by
    refine AnalyticAt.inv ?_ (by simpa using hw)
    fun_prop
  have hpow : taylorCoeffZero (fun t : ℂ => t ^ (1 : ℕ) * (w - t)⁻¹) m
      = if 1 ≤ m then taylorCoeffZero (fun t : ℂ => (w - t)⁻¹) (m - 1) else 0 :=
    taylorCoeffZero_pow_mul hker 1 m
  simp only [pow_one] at hpow
  rw [hpow, if_pos hm, taylorCoeffZero_inv_sub hw]
  congr 1
  omega

/-! ## The general residue -/

/-- **The residue against the Cauchy kernel is the principal part at `Z`.** -/
theorem laurentCoeff_mul_inv_sub {H : ℂ → ℂ} {ρ Z : ℂ} (hZ : Z ≠ ρ) {k : ℕ}
    (hk : AnalyticAt ℂ (laurentShift H ρ k) 0) :
    laurentCoeff (fun s : ℂ => H s * (Z - s)⁻¹) ρ (-1) = principalPart H ρ k Z := by
  classical
  obtain ⟨g, hg, hsplit⟩ := eq_add_principalPart hk
  have hZρ : Z - ρ ≠ 0 := sub_ne_zero.2 hZ
  -- the meromorphic pieces
  have hkerA : AnalyticAt ℂ (fun s : ℂ => (Z - s)⁻¹) ρ := by
    refine AnalyticAt.inv ?_ hZρ
    fun_prop
  have hmeroH : MeromorphicAt H ρ :=
    (meromorphicAt_iff_exists_analyticAt_laurentShift H ρ).2 ⟨k, hk⟩
  have hterm : ∀ j : ℕ, MeromorphicAt
      (fun s : ℂ => ((s - ρ) ^ (k - j))⁻¹ * (Z - s)⁻¹) ρ := by
    intro j
    have h1 : MeromorphicAt (fun s : ℂ => ((s - ρ) ^ (k - j))⁻¹) ρ := by
      refine MeromorphicAt.inv ?_
      exact ((analyticAt_id.sub analyticAt_const).pow _).meromorphicAt
    exact h1.mul hkerA.meromorphicAt
  -- split the integrand
  have hev : (fun s : ℂ => H s * (Z - s)⁻¹)
      =ᶠ[𝓝[≠] ρ] fun s : ℂ => g s * (Z - s)⁻¹
        + ∑ j ∈ Finset.range k,
            laurentCoeff H ρ ((j : ℤ) - k) * (((s - ρ) ^ (k - j))⁻¹ * (Z - s)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hsne : s ≠ ρ := by simpa using hs
    rw [hsplit s hsne, principalPart]
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hmero1 : MeromorphicAt (fun s : ℂ => H s * (Z - s)⁻¹) ρ :=
    hmeroH.mul hkerA.meromorphicAt
  rw [laurentCoeff_congr hmero1 hev]
  have hmeroG : MeromorphicAt (fun s : ℂ => g s * (Z - s)⁻¹) ρ :=
    (hg.mul hkerA).meromorphicAt
  have hmeroS : MeromorphicAt (fun s : ℂ => ∑ j ∈ Finset.range k,
      laurentCoeff H ρ ((j : ℤ) - k) * (((s - ρ) ^ (k - j))⁻¹ * (Z - s)⁻¹)) ρ := by
    exact MeromorphicAt.fun_sum (fun j _ => (analyticAt_const.meromorphicAt).mul (hterm j))
  rw [laurentCoeff_add hmeroG hmeroS]
  have hgzero : laurentCoeff (fun s : ℂ => g s * (Z - s)⁻¹) ρ (-1) = 0 :=
    laurentCoeff_eq_zero_of_analyticAt (hg.mul hkerA) (by norm_num)
  rw [hgzero, zero_add,
    laurentCoeff_sum (Finset.range k)
      (fun j => fun s : ℂ => ((s - ρ) ^ (k - j))⁻¹ * (Z - s)⁻¹)
      (fun j => laurentCoeff H ρ ((j : ℤ) - k)) ρ (-1) (fun j _ => hterm j)]
  rw [principalPart]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hm : 1 ≤ k - j := by omega
  rw [laurentCoeff_inv_pow_mul_inv_sub hZ hm, inv_pow]

end

end GaloisForLFunctions.HTGeometry
