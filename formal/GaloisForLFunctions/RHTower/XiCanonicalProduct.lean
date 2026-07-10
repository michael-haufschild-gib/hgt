import GaloisForLFunctions.RHTower.CanonicalProduct
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# The canonical product on the actual Xi divisor

The index type below is the sigma type of Xi-divisor support points and their finite
multiplicity copies.  It therefore retains the divisor multiplicity exactly without choosing
an enumeration of the zero set.  The centered spectral coordinate sends a Xi zero `rho` to the
corresponding zero of `XiC z = xi (1/2 + z I)`.
-/

open Complex Metric Function Filter MeromorphicOn

namespace RHTower

noncomputable section

/-- The support of the global Xi divisor. -/
abbrev XiDivisorSupport :=
  ↥(MeromorphicOn.divisor xi Set.univ).support

/-- A Xi zero together with one of its divisor-multiplicity copies. -/
abbrev XiZeroCopy :=
  Σ ρ : XiDivisorSupport,
    Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)))

/-- The zero of `XiC` corresponding to a Xi-divisor point: if
`rho = 1/2 + z I`, then `z = (rho - 1/2)(-I)`. -/
def xiSpectralPoint (q : XiZeroCopy) : ℂ :=
  ((q.1 : ℂ) - 1 / 2) * (-Complex.I)

theorem xiSpectralPoint_ne_zero (q : XiZeroCopy) :
    xiSpectralPoint q ≠ 0 := by
  rw [xiSpectralPoint, mul_ne_zero_iff]
  exact ⟨sub_ne_zero.mpr (xi_divisor_support_ne_half q.1),
    neg_ne_zero.mpr Complex.I_ne_zero⟩

theorem norm_xiSpectralPoint (q : XiZeroCopy) :
    ‖xiSpectralPoint q‖ = ‖(q.1 : ℂ) - 1 / 2‖ := by
  rw [xiSpectralPoint, norm_mul, norm_neg, Complex.norm_I, mul_one]

/-- The reciprocal-square convergence condition for the genus-one product, now over the
actual multiplicity copies rather than a multiplicity-weighted support sum. -/
theorem xiSpectralPoint_inv_sq_summable :
    Summable (fun q : XiZeroCopy => 1 / ‖xiSpectralPoint q‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  constructor
  · intro ρ
    exact (hasSum_fintype _).summable
  · refine xi_zero_multiplicity_centered_inv_sq_summable.congr (fun ρ => ?_)
    symm
    rw [tsum_fintype]
    simp only [norm_xiSpectralPoint]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnonneg : 0 ≤ (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) :=
      le_of_lt (xi_divisor_pos_on_support ρ)
    have hcast : (((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)).toNat : ℝ) =
        ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hcast, div_eq_mul_inv]
    ring

theorem XiC_xiSpectralPoint_eq_zero (q : XiZeroCopy) :
    XiC (xiSpectralPoint q) = 0 := by
  rw [XiC, xiSpectralPoint]
  have harg : (1 : ℂ) / 2 + (((q.1 : ℂ) - 1 / 2) * (-I)) * I = q.1 := by
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [mul_assoc, hI, mul_one]
    ring
  rw [harg]
  exact xi_eq_zero_of_mem_divisor_support q.1

/-- Under RH every multiplicity copy gives a real zero of `XiC`. -/
theorem xiSpectralPoint_real_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    ∃ t : ℝ, xiSpectralPoint q = (t : ℂ) := by
  refine ⟨(q.1 : ℂ).im, ?_⟩
  apply Complex.ext
  · simp [xiSpectralPoint]
  · simp [xiSpectralPoint, xi_divisor_support_re_eq_half_of_rh hRH q.1]

/-- The genus-one canonical product formed from every Xi zero with its exact divisor
multiplicity. -/
noncomputable def xiCanonicalProduct : ℂ → ℂ :=
  canonicalProductE1Indexed xiSpectralPoint

theorem xiCanonicalProduct_hasProdLocallyUniformlyOn :
    HasProdLocallyUniformlyOn
      (fun q z => weierstrassE1 (z / xiSpectralPoint q))
      xiCanonicalProduct Set.univ :=
  canonicalProductE1Indexed_hasProdLocallyUniformlyOn xiSpectralPoint
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable

theorem xiCanonicalProduct_analytic :
    AnalyticOnNhd ℂ xiCanonicalProduct Set.univ :=
  canonicalProductE1Indexed_analytic xiSpectralPoint
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable

/-- Every indexed divisor copy is a zero of the canonical product. -/
theorem xiCanonicalProduct_eq_zero (q : XiZeroCopy) :
    xiCanonicalProduct (xiSpectralPoint q) = 0 := by
  rw [xiCanonicalProduct, canonicalProductE1Indexed]
  apply tprod_of_exists_eq_zero
  refine ⟨q, ?_⟩
  rw [div_self (xiSpectralPoint_ne_zero q), weierstrassE1_one]

/-- The canonical product has exactly the prescribed divisor-copy locations as its zeros. -/
theorem xiCanonicalProduct_eq_zero_iff_exists (z : ℂ) :
    xiCanonicalProduct z = 0 ↔ ∃ q : XiZeroCopy, xiSpectralPoint q = z := by
  constructor
  · intro hz
    by_contra hnone
    have haway : ∀ q : XiZeroCopy, z ≠ xiSpectralPoint q := by
      intro q heq
      exact hnone ⟨q, heq.symm⟩
    exact (canonicalProductE1Indexed_ne_zero xiSpectralPoint
      xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable haway) hz
  · rintro ⟨q, rfl⟩
    exact xiCanonicalProduct_eq_zero q

/-- The actual zeros of `XiC` are exactly the centered spectral locations supplied by the
Xi divisor, including at least one multiplicity copy at each support point. -/
theorem XiC_eq_zero_iff_exists_xiZeroCopy (z : ℂ) :
    XiC z = 0 ↔ ∃ q : XiZeroCopy, xiSpectralPoint q = z := by
  constructor
  · intro hz
    have hzero : xi (1 / 2 + z * I) = 0 := by simpa only [XiC] using hz
    have hmem := mem_xi_divisor_support_of_eq_zero hzero
    let ρ : XiDivisorSupport := ⟨1 / 2 + z * I, hmem⟩
    have hpos := xi_divisor_pos_on_support ρ
    have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
      omega
    let q : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
    refine ⟨q, ?_⟩
    dsimp only [q, ρ, xiSpectralPoint]
    rw [sub_eq_add_neg]
    ring_nf
    rw [I_sq]
    ring
  · rintro ⟨q, rfl⟩
    exact XiC_xiSpectralPoint_eq_zero q

/-- The canonical product and `XiC` have the same zero set. -/
theorem xiCanonicalProduct_eq_zero_iff_XiC_eq_zero (z : ℂ) :
    xiCanonicalProduct z = 0 ↔ XiC z = 0 := by
  rw [xiCanonicalProduct_eq_zero_iff_exists, XiC_eq_zero_iff_exists_xiZeroCopy]

end

end RHTower
