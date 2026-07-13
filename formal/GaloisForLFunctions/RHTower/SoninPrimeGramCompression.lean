import GaloisForLFunctions.RHTower.SoninEulerFiniteGramLower
import GaloisForLFunctions.RHTower.XiPrimeSeamPairVariance

/-!
# Finite prime Gram compression from common Sonin shells

The paired common-shell construction does more than detect one Gram entry at a time.  Its input
shells are asymptotically an orthonormal finite family.  Consequently every zero-diagonal finite
prime matrix is compressed, modulo compact operators, with its full finite-dimensional operator
norm.

This removes the Hilbert-tensor-product interface from the prime-seam exterior route.  The
antisymmetric pair matrix can be tested on the one-particle Gram commutator itself.
-/

noncomputable section

open MeasureTheory Set
open Filter Topology
open scoped InnerProduct InnerProductSpace BigOperators

namespace RHTower

theorem real_prime_one_lt {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) :
    ∀ i, (1 : ℝ) < (p i : ℝ) := by
  intro i
  exact_mod_cast (hp i).one_lt

/-- Ratio separation of the active Gram shells also separates the inverse-dilated input shells. -/
theorem inverseDilatedEvenShellEven_orthonormal_scales_of_ratioSeparation
    {n : ℕ} (c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hinj : Function.Injective r) (hc : 0 < c) (hcd : c < d)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex r,
      finiteActiveScaleRatio r z < finiteActiveScaleRatio r w →
        d * finiteActiveScaleRatio r z < c * finiteActiveScaleRatio r w)
    (m : ℕ) :
    Orthonormal ℂ (fun i => inverseDilatedEvenShellEven c d (r i) hc hcd (hr i) m) := by
  constructor
  · intro i
    exact (inverseDilatedEvenShellEven_orthonormal c d (r i) hc hcd (hr i)).norm_eq_one m
  · intro i j hij
    have hrne : r i ≠ r j := fun h => hij (hinj h)
    rcases lt_or_gt_of_ne hrne with hlt | hgt
    · let z : finiteActiveScaleRatioIndex r := ⟨(i, i), le_rfl⟩
      let w : finiteActiveScaleRatioIndex r := ⟨(j, i), hlt.le⟩
      have hri0 : 0 < r i := zero_lt_one.trans (hr i)
      have hrj0 : 0 < r j := zero_lt_one.trans (hr j)
      have hratio : finiteActiveScaleRatio r z < finiteActiveScaleRatio r w := by
        dsimp [z, w, finiteActiveScaleRatio]
        rw [div_self (ne_of_gt hri0)]
        exact (one_lt_div hri0).mpr hlt
      have hscaled := hsep z w hratio
      have hband : d * (r j)⁻¹ < c * (r i)⁻¹ := by
        dsimp [z, w, finiteActiveScaleRatio] at hscaled
        rw [div_self (ne_of_gt hri0)] at hscaled
        have hscaled' : d < c * (r j / r i) := by simpa only [mul_one] using hscaled
        have hrij : d * r i < c * r j := by
          calc
            d * r i < (c * (r j / r i)) * r i :=
              mul_lt_mul_of_pos_right hscaled' hri0
            _ = c * r j := by field_simp
        simpa [div_eq_mul_inv] using (div_lt_div_iff₀ hrj0 hri0).2 hrij
      rw [← inner_conj_symm]
      have hzero : inner ℂ
          (inwardDilatedEvenShellEven c d (r j)⁻¹ hc hcd (inv_pos.mpr hrj0) m)
          (inwardDilatedEvenShellEven c d (r i)⁻¹ hc hcd (inv_pos.mpr hri0) m) = 0 := by
        change inner ℂ
          (inwardDilatedEvenShell c d (r j)⁻¹ hc hcd (inv_pos.mpr hrj0) m)
          (inwardDilatedEvenShell c d (r i)⁻¹ hc hcd (inv_pos.mpr hri0) m) = 0
        exact inner_inwardDilatedEvenShell_eq_zero_of_lt hc hcd
          (inv_pos.mpr hrj0) (inv_pos.mpr hri0) hband m
      have hinvzero : inner ℂ
          (inverseDilatedEvenShellEven c d (r j) hc hcd (hr j) m)
          (inverseDilatedEvenShellEven c d (r i) hc hcd (hr i) m) = 0 := by
        simpa only [inverseDilatedEvenShellEven, inwardDilatedEvenShellEven] using hzero
      rw [hinvzero]
      simp
    · let z : finiteActiveScaleRatioIndex r := ⟨(j, j), le_rfl⟩
      let w : finiteActiveScaleRatioIndex r := ⟨(i, j), hgt.le⟩
      have hri0 : 0 < r i := zero_lt_one.trans (hr i)
      have hrj0 : 0 < r j := zero_lt_one.trans (hr j)
      have hratio : finiteActiveScaleRatio r z < finiteActiveScaleRatio r w := by
        dsimp [z, w, finiteActiveScaleRatio]
        rw [div_self (ne_of_gt hrj0)]
        exact (one_lt_div hrj0).mpr hgt
      have hscaled := hsep z w hratio
      have hband : d * (r i)⁻¹ < c * (r j)⁻¹ := by
        dsimp [z, w, finiteActiveScaleRatio] at hscaled
        rw [div_self (ne_of_gt hrj0)] at hscaled
        have hscaled' : d < c * (r i / r j) := by simpa only [mul_one] using hscaled
        have hrji : d * r j < c * r i := by
          calc
            d * r j < (c * (r i / r j)) * r j :=
              mul_lt_mul_of_pos_right hscaled' hrj0
            _ = c * r i := by field_simp
        simpa [div_eq_mul_inv] using (div_lt_div_iff₀ hri0 hrj0).2 hrji
      have hzero : inner ℂ
          (inwardDilatedEvenShellEven c d (r i)⁻¹ hc hcd (inv_pos.mpr hri0) m)
          (inwardDilatedEvenShellEven c d (r j)⁻¹ hc hcd (inv_pos.mpr hrj0) m) = 0 := by
        change inner ℂ
          (inwardDilatedEvenShell c d (r i)⁻¹ hc hcd (inv_pos.mpr hri0) m)
          (inwardDilatedEvenShell c d (r j)⁻¹ hc hcd (inv_pos.mpr hrj0) m) = 0
        exact inner_inwardDilatedEvenShell_eq_zero_of_lt hc hcd
          (inv_pos.mpr hri0) (inv_pos.mpr hrj0) hband m
      simpa only [inverseDilatedEvenShellEven, inwardDilatedEvenShellEven] using hzero

/-- A finite linear combination of the paired Sonin input shells. -/
def finitePairedEvenSoninInputCombination
    {n : ℕ} (a c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d) (x : Fin n → ℂ) (m : ℕ) : evenSubspace :=
  ∑ i, x i • finitePairedEvenSoninInput a c d r hr hc hcd i m

/-- Paired input combinations converge to the corresponding raw inverse-shell combinations. -/
theorem finitePairedEvenSoninInputCombination_tendsto_raw
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d) (harc : ∀ i, a < r i * c) (x : Fin n → ℂ) :
    Tendsto (fun m => ‖finitePairedEvenSoninInputCombination a c d r hr hc hcd x m -
      ∑ i, x i • inverseDilatedEvenShellEven c d (r i) hc hcd (hr i) m‖)
      atTop (nhds 0) := by
  have hi : ∀ i, Tendsto (fun m => x i •
      (finitePairedEvenSoninInput a c d r hr hc hcd i m -
        inverseDilatedEvenShellEven c d (r i) hc hcd (hr i) m)) atTop (nhds 0) := by
    intro i
    have h := evenCentralSoninProjection_inverseDilatedEvenShell_tendsto
      a c d (r i) ha hc hcd (hr i) (harc i)
    have hv : Tendsto (fun m =>
        finitePairedEvenSoninInput a c d r hr hc hcd i m -
          inverseDilatedEvenShellEven c d (r i) hc hcd (hr i) m) atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (by
        simpa [finitePairedEvenSoninInput] using h)
    simpa only [smul_zero] using hv.const_smul (x i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hsum0 : Tendsto (fun m => ∑ i, x i •
      (finitePairedEvenSoninInput a c d r hr hc hcd i m -
        inverseDilatedEvenShellEven c d (r i) hc hcd (hr i) m)) atTop (nhds 0) := by
    simpa using hsum
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  convert hsum0 using 1
  funext m
  simp only [finitePairedEvenSoninInputCombination]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib]

/-- The norm of a finite paired-input combination tends to its Euclidean coefficient norm. -/
theorem norm_finitePairedEvenSoninInputCombination_tendsto
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hinj : Function.Injective r) (hc : 0 < c) (hcd : c < d)
    (harc : ∀ i, a < r i * c)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex r,
      finiteActiveScaleRatio r z < finiteActiveScaleRatio r w →
        d * finiteActiveScaleRatio r z < c * finiteActiveScaleRatio r w)
    (x : Fin n → ℂ) :
    Tendsto (fun m => ‖finitePairedEvenSoninInputCombination a c d r hr hc hcd x m‖)
      atTop (nhds (finiteCoefficientL2Norm x)) := by
  let g : ℕ → evenSubspace := fun m =>
    ∑ i, x i • inverseDilatedEvenShellEven c d (r i) hc hcd (hr i) m
  have happrox := finitePairedEvenSoninInputCombination_tendsto_raw
    a c d ha r hr hc hcd harc x
  have hnorm : ∀ m, ‖g m‖ = finiteCoefficientL2Norm x := by
    intro m
    apply norm_sum_smul_orthonormal_eq_finiteCoefficientL2Norm
    exact inverseDilatedEvenShellEven_orthonormal_scales_of_ratioSeparation
      c d r hr hinj hc hcd hsep m
  exact tendsto_norm_of_norm_sub_tendsto_zero_of_norm_eq
    (by simpa [g] using happrox) hnorm

/-- A paired-input combination is bounded by the coefficient `l1` norm, uniformly in the shell
index. -/
theorem norm_finitePairedEvenSoninInputCombination_le
    {n : ℕ} (a c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d) (x : Fin n → ℂ) (m : ℕ) :
    ‖finitePairedEvenSoninInputCombination a c d r hr hc hcd x m‖ ≤ ∑ i, ‖x i‖ := by
  rw [finitePairedEvenSoninInputCombination]
  calc
    ‖∑ i, x i • finitePairedEvenSoninInput a c d r hr hc hcd i m‖ ≤
        ∑ i, ‖x i • finitePairedEvenSoninInput a c d r hr hc hcd i m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, ‖x i‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg (x i))
        (norm_finitePairedEvenSoninInput_le_one a c d r hr hc hcd i m)

/-- Every fixed finite paired-input combination is weakly null. -/
theorem finitePairedEvenSoninInputCombination_weakly_tendsto_zero
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d) (harc : ∀ i, a < r i * c) (x : Fin n → ℂ) :
    ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun m => ℓ (finitePairedEvenSoninInputCombination a c d r hr hc hcd x m))
        atTop (nhds 0) := by
  intro ℓ
  have hi : ∀ i, Tendsto (fun m =>
      ℓ (x i • finitePairedEvenSoninInput a c d r hr hc hcd i m))
      atTop (nhds 0) := by
    intro i
    have h := finitePairedEvenSoninInput_weakly_tendsto_zero
      a c d r hr ha hc hcd harc i ℓ
    simpa only [map_smul, smul_zero] using h.const_smul (x i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  simpa [finitePairedEvenSoninInputCombination, map_sum] using hsum

/-- The finite-dimensional sesquilinear form compressed by a Gram matrix. -/
def finiteMatrixBilinear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x y : Fin n → ℂ) : ℂ :=
  ∑ l, ∑ k, star (y l) * x k * A l k

/-- For a zero-diagonal prime matrix, every paired-shell compression coefficient is the literal
matrix entry, including on the diagonal. -/
theorem finitePrimeGram_pairedShell_inner_tendsto_matrixEntry_of_diagonal_zero
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (harc : ∀ i, a < (p i : ℝ) * c)
    (hout : ∀ i j, (p i : ℝ) < p j → a * p i < c * p j)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex (fun i => (p i : ℝ)),
      finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          finiteActiveScaleRatio (fun i => (p i : ℝ)) w →
        d * finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          c * finiteActiveScaleRatio (fun i => (p i : ℝ)) w)
    (A : Matrix (Fin n) (Fin n) ℂ) (hdiag : ∀ i, A i i = 0) (k l : Fin n) :
    Tendsto (fun m => ‖inner ℂ
      (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) hc hcd l m)
      (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) A
        (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hc hcd k m)) - A l k‖)
      atTop (nhds 0) := by
  let r : Fin n → ℝ := fun i => (p i : ℝ)
  let hr : ∀ i, 1 < r i := real_prime_one_lt p hp
  change Tendsto (fun m => ‖inner ℂ
      (finitePairedEvenSoninInput a c d r hr hc hcd l m)
      (finiteEvenDilationGramCombination a r hr A
        (finitePairedEvenSoninInput a c d r hr hc hcd k m)) - A l k‖)
      atTop (nhds 0)
  have hbase := finiteEvenDilationGramCombination_pairedShell_inner_tendsto
    a c d ha hc hcd hda r hr harc hout A k l
  convert hbase using 1
  funext m
  by_cases hkl : k ≠ l
  · rw [finiteGramShellCoefficient_prime_offDiagonal_eq
      c d p hp hinj hc hcd (by simpa [r] using hsep) A k l hkl m]
  · have hkeq : k = l := not_ne_iff.mp hkl
    subst l
    rw [finiteGramShellCoefficient_prime_diagonal_eq
      c d p hp hinj hc hcd (by simpa [r] using hsep) A k m]
    simp [finitePrimeDiagonalTail, hdiag]

/-- Finite paired-input combinations compress a zero-diagonal prime Gram matrix to its full
finite sesquilinear form. -/
theorem finitePrimeGram_pairedCombination_inner_tendsto_bilinear
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d) (hda : d < a)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (harc : ∀ i, a < (p i : ℝ) * c)
    (hout : ∀ i j, (p i : ℝ) < p j → a * p i < c * p j)
    (hsep : ∀ z w : finiteActiveScaleRatioIndex (fun i => (p i : ℝ)),
      finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          finiteActiveScaleRatio (fun i => (p i : ℝ)) w →
        d * finiteActiveScaleRatio (fun i => (p i : ℝ)) z <
          c * finiteActiveScaleRatio (fun i => (p i : ℝ)) w)
    (A : Matrix (Fin n) (Fin n) ℂ) (hdiag : ∀ i, A i i = 0)
    (x y : Fin n → ℂ) :
    Tendsto (fun m => inner ℂ
      (finitePairedEvenSoninInputCombination a c d (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) hc hcd y m)
      (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) A
        (finitePairedEvenSoninInputCombination a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hc hcd x m)))
      atTop (nhds (finiteMatrixBilinear A x y)) := by
  have hlk : ∀ l k, Tendsto (fun m => star (y l) * x k * inner ℂ
      (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) hc hcd l m)
      (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) A
        (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hc hcd k m)))
      atTop (nhds (star (y l) * x k * A l k)) := by
    intro l k
    have hz := finitePrimeGram_pairedShell_inner_tendsto_matrixEntry_of_diagonal_zero
      a c d ha hc hcd hda p hp hinj harc hout hsep A hdiag k l
    have hv : Tendsto (fun m => inner ℂ
        (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hc hcd l m)
        (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) A
          (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
            (real_prime_one_lt p hp) hc hcd k m)) - A l k)
        atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hz
    have hentry : Tendsto (fun m =>
        (inner ℂ
          (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
            (real_prime_one_lt p hp) hc hcd l m)
          (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
            (real_prime_one_lt p hp) A
            (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
              (real_prime_one_lt p hp) hc hcd k m)) - A l k) + A l k)
        atTop (nhds (0 + A l k)) := hv.add tendsto_const_nhds
    have hscaled := (hentry.const_mul (x k)).const_mul (star (y l))
    simpa [mul_assoc] using hscaled
  have hsum := tendsto_finsetSum Finset.univ (fun l _ =>
    tendsto_finsetSum Finset.univ (fun k _ => hlk l k))
  convert hsum using 1
  · funext m
    simp only [finitePairedEvenSoninInputCombination]
    rw [map_sum, sum_inner]
    apply Finset.sum_congr rfl
    intro l hl
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul]
    change inner ℂ
      (y l • ((finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) hc hcd l m : evenSubspace) : SoninL2))
      (x k • (((finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) A)
        (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hc hcd k m) : evenSubspace) : SoninL2)) =
      star (y l) * x k * inner ℂ
        ((finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hc hcd l m : evenSubspace) : SoninL2)
        (((finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) A)
          (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
            (real_prime_one_lt p hp) hc hcd k m) : evenSubspace) : SoninL2)
    rw [inner_smul_left, inner_smul_right, starRingEnd_apply]
    ring

/-- **Full finite prime Gram compression modulo compacts.**  A zero-diagonal matrix is detected
through every finite sesquilinear test, with the Euclidean input norms and no loss depending on the
number of primes. -/
theorem norm_finiteMatrixBilinear_le_norm_finitePrimeEvenDilationGram_sub_compact
    {n : ℕ} [Nonempty (Fin n)] (a : ℝ) (ha : 0 < a)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) (hdiag : ∀ i, A i i = 0)
    (x y : Fin n → ℂ) (K : evenSubspace →L[ℂ] evenSubspace)
    (hK : IsCompactOperator K) :
    ‖finiteMatrixBilinear A x y‖ ≤
      finiteCoefficientL2Norm y * finiteCoefficientL2Norm x *
        ‖finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) A - K‖ := by
  let r : Fin n → ℝ := fun i => (p i : ℝ)
  let hr : ∀ i, 1 < r i := real_prime_one_lt p hp
  have hrInj : Function.Injective r := by
    intro i j hij
    apply hinj
    change (p i : ℝ) = (p j : ℝ) at hij
    exact_mod_cast hij
  obtain ⟨c, d, hc, hcd, hda, harc, hout, hsep⟩ :=
    exists_finiteScale_gramSeparatingInteriorShell a ha r hr
  let fx : ℕ → evenSubspace := fun m =>
    finitePairedEvenSoninInputCombination a c d r hr hc hcd x m
  let fy : ℕ → evenSubspace := fun m =>
    finitePairedEvenSoninInputCombination a c d r hr hc hcd y m
  let T : evenSubspace →L[ℂ] evenSubspace :=
    finiteEvenDilationGramCombination a r hr A
  have hxNorm : Tendsto (fun m => ‖fx m‖) atTop (nhds (finiteCoefficientL2Norm x)) := by
    simpa [fx] using norm_finitePairedEvenSoninInputCombination_tendsto
      a c d ha r hr hrInj hc hcd harc hsep x
  have hyNorm : Tendsto (fun m => ‖fy m‖) atTop (nhds (finiteCoefficientL2Norm y)) := by
    simpa [fy] using norm_finitePairedEvenSoninInputCombination_tendsto
      a c d ha r hr hrInj hc hcd harc hsep y
  have hinner : Tendsto (fun m => inner ℂ (fy m) (T (fx m)))
      atTop (nhds (finiteMatrixBilinear A x y)) := by
    simpa [fx, fy, T, r, hr] using
      finitePrimeGram_pairedCombination_inner_tendsto_bilinear
        a c d ha hc hcd hda p hp hinj
          (by simpa [r] using harc) (by simpa [r] using hout)
          (by simpa [r] using hsep) A hdiag x y
  have hinnerNorm : Tendsto (fun m => ‖inner ℂ (fy m) (T (fx m))‖)
      atTop (nhds ‖finiteMatrixBilinear A x y‖) := hinner.norm
  have hxWeak : ∀ ℓ : evenSubspace →L[ℂ] ℂ,
      Tendsto (fun m => ℓ (fx m)) atTop (nhds 0) := by
    simpa [fx] using finitePairedEvenSoninInputCombination_weakly_tendsto_zero
      a c d ha r hr hc hcd harc x
  have hxBound : ∀ m, ‖fx m‖ ≤ ∑ i, ‖x i‖ := by
    intro m
    simpa [fx] using norm_finitePairedEvenSoninInputCombination_le
      a c d r hr hc hcd x m
  have hKzero : Tendsto (fun m => ‖K (fx m)‖) atTop (nhds 0) :=
    IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null
      K hK fx (∑ i, ‖x i‖) hxBound hxWeak
  have hupper : Tendsto (fun m =>
      ‖fy m‖ * (‖T - K‖ * ‖fx m‖ + ‖K (fx m)‖)) atTop
      (nhds (finiteCoefficientL2Norm y *
        (‖T - K‖ * finiteCoefficientL2Norm x + 0))) :=
    hyNorm.mul ((tendsto_const_nhds.mul hxNorm).add hKzero)
  have hle : ∀ m, ‖inner ℂ (fy m) (T (fx m))‖ ≤
      ‖fy m‖ * (‖T - K‖ * ‖fx m‖ + ‖K (fx m)‖) := by
    intro m
    have hdecomp : T (fx m) = (T - K) (fx m) + K (fx m) := by simp
    have hfirst : ‖inner ℂ (fy m) ((T - K) (fx m))‖ ≤
        ‖fy m‖ * ‖(T - K) (fx m)‖ := by
      change ‖inner ℂ ((fy m : evenSubspace) : SoninL2)
          ((((T - K) (fx m) : evenSubspace) : SoninL2))‖ ≤
        ‖((fy m : evenSubspace) : SoninL2)‖ *
          ‖((((T - K) (fx m) : evenSubspace) : SoninL2))‖
      exact norm_inner_le_norm _ _
    have hsecond : ‖inner ℂ (fy m) (K (fx m))‖ ≤
        ‖fy m‖ * ‖K (fx m)‖ := by
      change ‖inner ℂ ((fy m : evenSubspace) : SoninL2)
          (((K (fx m) : evenSubspace) : SoninL2))‖ ≤
        ‖((fy m : evenSubspace) : SoninL2)‖ *
          ‖((K (fx m) : evenSubspace) : SoninL2)‖
      exact norm_inner_le_norm _ _
    rw [hdecomp, inner_add_right]
    calc
      ‖inner ℂ (fy m) ((T - K) (fx m)) + inner ℂ (fy m) (K (fx m))‖ ≤
          ‖inner ℂ (fy m) ((T - K) (fx m))‖ +
            ‖inner ℂ (fy m) (K (fx m))‖ := norm_add_le _ _
      _ ≤ ‖fy m‖ * ‖(T - K) (fx m)‖ + ‖fy m‖ * ‖K (fx m)‖ :=
        add_le_add hfirst hsecond
      _ ≤ ‖fy m‖ * (‖T - K‖ * ‖fx m‖ + ‖K (fx m)‖) := by
        have hop := (T - K).le_opNorm (fx m)
        have hfy : 0 ≤ ‖fy m‖ := norm_nonneg _
        nlinarith
  have hlimit := le_of_tendsto_of_tendsto hinnerNorm hupper (Eventually.of_forall hle)
  change ‖finiteMatrixBilinear A x y‖ ≤
    finiteCoefficientL2Norm y * finiteCoefficientL2Norm x * ‖T - K‖
  simpa [mul_comm, mul_left_comm, mul_assoc] using hlimit

/-- Matrix-vector multiplication in the finite coefficient carrier. -/
def finiteMatrixMulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (x : Fin n → ℂ) (i : Fin n) : ℂ :=
  ∑ j, A i j * x j

theorem finiteMatrixBilinear_mulVec
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    finiteMatrixBilinear A x (finiteMatrixMulVec A x) =
      ((∑ i, ‖finiteMatrixMulVec A x i‖ ^ 2 : ℝ) : ℂ) := by
  classical
  unfold finiteMatrixBilinear
  rw [show ((∑ i, ‖finiteMatrixMulVec A x i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ((‖finiteMatrixMulVec A x i‖ ^ 2 : ℝ) : ℂ) by
    push_cast
    rfl]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ k, star (finiteMatrixMulVec A x i) * x k * A i k) =
        star (finiteMatrixMulVec A x i) * (∑ k, A i k * x k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (starRingEnd ℂ) (finiteMatrixMulVec A x i) *
        finiteMatrixMulVec A x i := by
      rw [finiteMatrixMulVec, starRingEnd_apply]
    _ = (Complex.normSq (finiteMatrixMulVec A x i) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self]
    _ = ((‖finiteMatrixMulVec A x i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.sq_norm]

theorem finiteCoefficientL2Norm_sq {n : ℕ} (x : Fin n → ℂ) :
    finiteCoefficientL2Norm x ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  unfold finiteCoefficientL2Norm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg ‖x i‖)

/-- The common-shell compression contains the full finite-dimensional matrix operator norm: the
Euclidean norm of every matrix-vector product survives every compact perturbation. -/
theorem finiteCoefficientL2Norm_matrixMulVec_le_norm_finitePrimeEvenDilationGram_sub_compact
    {n : ℕ} [Nonempty (Fin n)] (a : ℝ) (ha : 0 < a)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (A : Matrix (Fin n) (Fin n) ℂ) (hdiag : ∀ i, A i i = 0)
    (x : Fin n → ℂ) (K : evenSubspace →L[ℂ] evenSubspace)
    (hK : IsCompactOperator K) :
    finiteCoefficientL2Norm (finiteMatrixMulVec A x) ≤
      finiteCoefficientL2Norm x *
        ‖finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) A - K‖ := by
  let y : Fin n → ℂ := finiteMatrixMulVec A x
  let T : evenSubspace →L[ℂ] evenSubspace :=
    finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
      (real_prime_one_lt p hp) A
  have hbilinear :=
    norm_finiteMatrixBilinear_le_norm_finitePrimeEvenDilationGram_sub_compact
      a ha p hp hinj A hdiag x y K hK
  have hvalue : ‖finiteMatrixBilinear A x y‖ = finiteCoefficientL2Norm y ^ 2 := by
    rw [show finiteMatrixBilinear A x y =
        ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ) by
      simpa [y] using finiteMatrixBilinear_mulVec A x]
    rw [Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun i hi => sq_nonneg ‖y i‖)]
    exact (finiteCoefficientL2Norm_sq y).symm
  rw [hvalue] at hbilinear
  by_cases hy : finiteCoefficientL2Norm y = 0
  · rw [hy]
    have hn : 0 ≤
        ‖finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) A - K‖ := by positivity
    exact mul_nonneg (finiteCoefficientL2Norm_nonneg x) hn
  · have hypos : 0 < finiteCoefficientL2Norm y :=
      lt_of_le_of_ne (finiteCoefficientL2Norm_nonneg y) (Ne.symm hy)
    have hxnonneg := finiteCoefficientL2Norm_nonneg x
    have hopnonneg : 0 ≤ ‖T - K‖ := by positivity
    change finiteCoefficientL2Norm y ≤ finiteCoefficientL2Norm x * ‖T - K‖
    nlinarith

end RHTower
