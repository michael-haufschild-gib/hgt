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
    Orthonormal ℂ (fun i => inverseDilatedEvenShellEven c d (r i) hcd (hr i) m) := by
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
          (inwardDilatedEvenShellEven c d (r j)⁻¹ hcd (inv_pos.mpr hrj0) m)
          (inwardDilatedEvenShellEven c d (r i)⁻¹ hcd (inv_pos.mpr hri0) m) = 0 := by
        change inner ℂ
          (inwardDilatedEvenShell c d (r j)⁻¹ hcd (inv_pos.mpr hrj0) m)
          (inwardDilatedEvenShell c d (r i)⁻¹ hcd (inv_pos.mpr hri0) m) = 0
        exact inner_inwardDilatedEvenShell_eq_zero_of_lt hc hcd
          (inv_pos.mpr hrj0) (inv_pos.mpr hri0) hband m
      have hinvzero : inner ℂ
          (inverseDilatedEvenShellEven c d (r j) hcd (hr j) m)
          (inverseDilatedEvenShellEven c d (r i) hcd (hr i) m) = 0 := by
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
          (inwardDilatedEvenShellEven c d (r i)⁻¹ hcd (inv_pos.mpr hri0) m)
          (inwardDilatedEvenShellEven c d (r j)⁻¹ hcd (inv_pos.mpr hrj0) m) = 0 := by
        change inner ℂ
          (inwardDilatedEvenShell c d (r i)⁻¹ hcd (inv_pos.mpr hri0) m)
          (inwardDilatedEvenShell c d (r j)⁻¹ hcd (inv_pos.mpr hrj0) m) = 0
        exact inner_inwardDilatedEvenShell_eq_zero_of_lt hc hcd
          (inv_pos.mpr hri0) (inv_pos.mpr hrj0) hband m
      simpa only [inverseDilatedEvenShellEven, inwardDilatedEvenShellEven] using hzero

/-- A finite linear combination of the paired Sonin input shells. -/
def finitePairedEvenSoninInputCombination
    {n : ℕ} (a c d : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hcd : c < d) (x : Fin n → ℂ) (m : ℕ) : evenSubspace :=
  ∑ i, x i • finitePairedEvenSoninInput a c d r hr hcd i m

/-- Paired input combinations converge to the corresponding raw inverse-shell combinations. -/
theorem finitePairedEvenSoninInputCombination_tendsto_raw
    {n : ℕ} (a c d : ℝ) (ha : 0 < a) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (hc : 0 < c) (hcd : c < d) (harc : ∀ i, a < r i * c) (x : Fin n → ℂ) :
    Tendsto (fun m => ‖finitePairedEvenSoninInputCombination a c d r hr hcd x m -
      ∑ i, x i • inverseDilatedEvenShellEven c d (r i) hcd (hr i) m‖)
      atTop (nhds 0) := by
  have hi : ∀ i, Tendsto (fun m => x i •
      (finitePairedEvenSoninInput a c d r hr hcd i m -
        inverseDilatedEvenShellEven c d (r i) hcd (hr i) m)) atTop (nhds 0) := by
    intro i
    have h := evenCentralSoninProjection_inverseDilatedEvenShell_tendsto
      a c d (r i) ha hc hcd (hr i) (harc i)
    have hv : Tendsto (fun m =>
        finitePairedEvenSoninInput a c d r hr hcd i m -
          inverseDilatedEvenShellEven c d (r i) hcd (hr i) m) atTop (nhds 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (by
        simpa [finitePairedEvenSoninInput] using h)
    simpa only [smul_zero] using hv.const_smul (x i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hsum0 : Tendsto (fun m => ∑ i, x i •
      (finitePairedEvenSoninInput a c d r hr hcd i m -
        inverseDilatedEvenShellEven c d (r i) hcd (hr i) m)) atTop (nhds 0) := by
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
    Tendsto (fun m => ‖finitePairedEvenSoninInputCombination a c d r hr hcd x m‖)
      atTop (nhds (finiteCoefficientL2Norm x)) := by
  let g : ℕ → evenSubspace := fun m =>
    ∑ i, x i • inverseDilatedEvenShellEven c d (r i) hcd (hr i) m
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
    ‖finitePairedEvenSoninInputCombination a c d r hr hcd x m‖ ≤ ∑ i, ‖x i‖ := by
  rw [finitePairedEvenSoninInputCombination]
  calc
    ‖∑ i, x i • finitePairedEvenSoninInput a c d r hr hcd i m‖ ≤
        ∑ i, ‖x i • finitePairedEvenSoninInput a c d r hr hcd i m‖ :=
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
      Tendsto (fun m => ℓ (finitePairedEvenSoninInputCombination a c d r hr hcd x m))
        atTop (nhds 0) := by
  intro ℓ
  have hi : ∀ i, Tendsto (fun m =>
      ℓ (x i • finitePairedEvenSoninInput a c d r hr hcd i m))
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
        (real_prime_one_lt p hp) hcd l m)
      (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) A
        (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hcd k m)) - A l k‖)
      atTop (nhds 0) := by
  let r : Fin n → ℝ := fun i => (p i : ℝ)
  let hr : ∀ i, 1 < r i := real_prime_one_lt p hp
  change Tendsto (fun m => ‖inner ℂ
      (finitePairedEvenSoninInput a c d r hr hcd l m)
      (finiteEvenDilationGramCombination a r hr A
        (finitePairedEvenSoninInput a c d r hr hcd k m)) - A l k‖)
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
        (real_prime_one_lt p hp) hcd y m)
      (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) A
        (finitePairedEvenSoninInputCombination a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hcd x m)))
      atTop (nhds (finiteMatrixBilinear A x y)) := by
  have hlk : ∀ l k, Tendsto (fun m => star (y l) * x k * inner ℂ
      (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) hcd l m)
      (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) A
        (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hcd k m)))
      atTop (nhds (star (y l) * x k * A l k)) := by
    intro l k
    have hz := finitePrimeGram_pairedShell_inner_tendsto_matrixEntry_of_diagonal_zero
      a c d ha hc hcd hda p hp hinj harc hout hsep A hdiag k l
    have hv : Tendsto (fun m => inner ℂ
        (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hcd l m)
        (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) A
          (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
            (real_prime_one_lt p hp) hcd k m)) - A l k)
        atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hz
    have hentry : Tendsto (fun m =>
        (inner ℂ
          (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
            (real_prime_one_lt p hp) hcd l m)
          (finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
            (real_prime_one_lt p hp) A
            (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
              (real_prime_one_lt p hp) hcd k m)) - A l k) + A l k)
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
        (real_prime_one_lt p hp) hcd l m : evenSubspace) : SoninL2))
      (x k • (((finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
        (real_prime_one_lt p hp) A)
        (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hcd k m) : evenSubspace) : SoninL2)) =
      star (y l) * x k * inner ℂ
        ((finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) hcd l m : evenSubspace) : SoninL2)
        (((finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) A)
          (finitePairedEvenSoninInput a c d (fun i => (p i : ℝ))
            (real_prime_one_lt p hp) hcd k m) : evenSubspace) : SoninL2)
    rw [inner_smul_left, inner_smul_right, starRingEnd_apply]
    ring
  · rfl

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
    finitePairedEvenSoninInputCombination a c d r hr hcd x m
  let fy : ℕ → evenSubspace := fun m =>
    finitePairedEvenSoninInputCombination a c d r hr hcd y m
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
      ((∑ i, ‖finiteMatrixMulVec A x i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  unfold finiteMatrixBilinear
  rw [show ((∑ i, ‖finiteMatrixMulVec A x i‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      ∑ i, ((‖finiteMatrixMulVec A x i‖ ^ (2 : ℕ) : ℝ) : ℂ) by
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
    _ = ((‖finiteMatrixMulVec A x i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [Complex.sq_norm]

theorem finiteCoefficientL2Norm_sq {n : ℕ} (x : Fin n → ℂ) :
    finiteCoefficientL2Norm x ^ (2 : ℕ) = ∑ i, ‖x i‖ ^ (2 : ℕ) := by
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
  have hvalue : ‖finiteMatrixBilinear A x y‖ = finiteCoefficientL2Norm y ^ (2 : ℕ) := by
    rw [show finiteMatrixBilinear A x y =
        ((∑ i, ‖y i‖ ^ (2 : ℕ) : ℝ) : ℂ) by
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

/-! ### Reciprocal-weight difference specialization -/

def finiteWeightMass {n : ℕ} (w : Fin n → ℝ) : ℝ := ∑ i, w i

def finiteWeightedNormSq {n : ℕ} (w : Fin n → ℝ) (u : Fin n → ℂ) : ℝ :=
  ∑ i, w i * ‖u i‖ ^ (2 : ℕ)

def finiteWeightedMean {n : ℕ} (w : Fin n → ℝ) (u : Fin n → ℂ) : ℂ :=
  ∑ i, ((w i : ℝ) : ℂ) * u i

def finiteWeightedDifferenceEnergy {n : ℕ}
    (w : Fin n → ℝ) (u : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, w i * w j * ‖u i - u j‖ ^ (2 : ℕ)

/-- Finite complex weighted variance on a `Fin` carrier. -/
theorem finiteWeightedDifferenceEnergy_eq_variance
    {n : ℕ} (w : Fin n → ℝ) (u : Fin n → ℂ) :
    finiteWeightedDifferenceEnergy w u =
      2 * finiteWeightMass w * finiteWeightedNormSq w u -
        2 * ‖finiteWeightedMean w u‖ ^ (2 : ℕ) := by
  have hre0 := two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion
    (Finset.univ : Finset (Fin n)) w (fun i => (u i).re) (fun i => (u i).re)
  have him0 := two_mul_weightedBilinear_eq_rankOne_add_pairwiseDispersion
    (Finset.univ : Finset (Fin n)) w (fun i => (u i).im) (fun i => (u i).im)
  have hre :
      2 * (∑ i, w i) * (∑ i, w i * (u i).re ^ (2 : ℕ)) =
        2 * (∑ i, w i * (u i).re) ^ (2 : ℕ) +
          ∑ i, ∑ j, w i * w j * ((u i).re - (u j).re) ^ (2 : ℕ) := by
    simpa only [pow_two, mul_assoc] using hre0
  have him :
      2 * (∑ i, w i) * (∑ i, w i * (u i).im ^ (2 : ℕ)) =
        2 * (∑ i, w i * (u i).im) ^ (2 : ℕ) +
          ∑ i, ∑ j, w i * w j * ((u i).im - (u j).im) ^ (2 : ℕ) := by
    simpa only [pow_two, mul_assoc] using him0
  have hmeanRe : (finiteWeightedMean w u).re = ∑ i, w i * (u i).re := by
    simp [finiteWeightedMean]
  have hmeanIm : (finiteWeightedMean w u).im = ∑ i, w i * (u i).im := by
    simp [finiteWeightedMean]
  have hrePair :
      (∑ i, ∑ j, w i * w j *
        (((u i).re - (u j).re) * ((u i).re - (u j).re))) =
      (2 * ∑ i, w i) * (∑ i, w i * (u i).re * (u i).re) -
        (2 * ∑ i, w i * (u i).re) * (∑ i, w i * (u i).re) := by
    rw [eq_sub_iff_add_eq']
    simpa only [mul_assoc] using hre0.symm
  have himPair :
      (∑ i, ∑ j, w i * w j *
        (((u i).im - (u j).im) * ((u i).im - (u j).im))) =
      (2 * ∑ i, w i) * (∑ i, w i * (u i).im * (u i).im) -
        (2 * ∑ i, w i * (u i).im) * (∑ i, w i * (u i).im) := by
    rw [eq_sub_iff_add_eq']
    simpa only [mul_assoc] using him0.symm
  unfold finiteWeightedDifferenceEnergy
  simp_rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    mul_add, Finset.sum_add_distrib]
  rw [hrePair, himPair]
  rw [hmeanRe, hmeanIm]
  unfold finiteWeightMass finiteWeightedNormSq
  simp_rw [Complex.sq_norm, Complex.normSq_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem sum_weighted_centered_sq
    {n : ℕ} (w a : Fin n → ℝ) :
    (∑ i, w i * ((∑ j, w j) * a i - ∑ j, w j * a j) ^ (2 : ℕ)) =
      (∑ i, w i) *
        ((∑ i, w i) * (∑ i, w i * a i ^ (2 : ℕ)) -
          (∑ i, w i * a i) ^ (2 : ℕ)) := by
  let M : ℝ := ∑ i, w i
  let A : ℝ := ∑ i, w i * a i
  let S : ℝ := ∑ i, w i * a i ^ (2 : ℕ)
  change (∑ i, w i * (M * a i - A) ^ (2 : ℕ)) = M * (M * S - A ^ (2 : ℕ))
  have h1 : (∑ i, M ^ (2 : ℕ) * (w i * a i ^ (2 : ℕ))) = M ^ (2 : ℕ) * S := by
    exact (Finset.mul_sum Finset.univ (fun i => w i * a i ^ (2 : ℕ)) (M ^ (2 : ℕ))).symm
  have h2 : (∑ i, (2 * M * A) * (w i * a i)) = (2 * M * A) * A := by
    exact (Finset.mul_sum Finset.univ (fun i => w i * a i) (2 * M * A)).symm
  have h3 : (∑ i, A ^ (2 : ℕ) * w i) = A ^ (2 : ℕ) * M := by
    exact (Finset.mul_sum Finset.univ w (A ^ (2 : ℕ))).symm
  calc
    (∑ i, w i * (M * a i - A) ^ (2 : ℕ)) =
        ∑ i, (M ^ (2 : ℕ) * (w i * a i ^ (2 : ℕ)) -
          (2 * M * A) * (w i * a i) + A ^ (2 : ℕ) * w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = M ^ (2 : ℕ) * S - (2 * M * A) * A + A ^ (2 : ℕ) * M := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, h2, h3]
    _ = M * (M * S - A ^ (2 : ℕ)) := by ring

/-- The zero-diagonal weighted difference matrix whose coefficient norm is the full pair
energy. -/
def finiteWeightedDifferenceMatrix {n : ℕ} (w : Fin n → ℝ) (u : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((Real.sqrt (w i) * Real.sqrt (w j) : ℝ) : ℂ) * (u i - u j)

/-- The square-root weight vector used to read weighted variance from the difference matrix. -/
def finiteSqrtWeightVector {n : ℕ} (w : Fin n → ℝ) : Fin n → ℂ :=
  fun i => ((Real.sqrt (w i) : ℝ) : ℂ)

theorem finiteWeightedDifferenceMatrix_diagonal
    {n : ℕ} (w : Fin n → ℝ) (u : Fin n → ℂ) (i : Fin n) :
    finiteWeightedDifferenceMatrix w u i i = 0 := by
  simp [finiteWeightedDifferenceMatrix]

theorem finiteCoefficientL2Norm_finiteSqrtWeightVector_sq
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    finiteCoefficientL2Norm (finiteSqrtWeightVector w) ^ (2 : ℕ) = finiteWeightMass w := by
  rw [finiteCoefficientL2Norm_sq]
  unfold finiteSqrtWeightVector finiteWeightMass
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw i)]

/-- Applying the weighted difference matrix to the square-root weight vector produces the
centered weighted packet. -/
theorem finiteWeightedDifferenceMatrix_mulVec_sqrtWeight
    {n : ℕ} (w : Fin n → ℝ) (u : Fin n → ℂ) (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    finiteMatrixMulVec (finiteWeightedDifferenceMatrix w u)
        (finiteSqrtWeightVector w) i =
      ((Real.sqrt (w i) : ℝ) : ℂ) *
        (((finiteWeightMass w : ℝ) : ℂ) * u i - finiteWeightedMean w u) := by
  unfold finiteMatrixMulVec finiteWeightedDifferenceMatrix finiteSqrtWeightVector
  unfold finiteWeightMass finiteWeightedMean
  calc
    (∑ j, ((Real.sqrt (w i) * Real.sqrt (w j) : ℝ) : ℂ) *
        (u i - u j) * (Real.sqrt (w j) : ℂ)) =
        ∑ j, ((Real.sqrt (w i) * w j : ℝ) : ℂ) * (u i - u j) := by
      apply Finset.sum_congr rfl
      intro j hj
      push_cast
      calc
        (Real.sqrt (w i) : ℂ) * (Real.sqrt (w j) : ℂ) * (u i - u j) *
            (Real.sqrt (w j) : ℂ) =
            (Real.sqrt (w i) : ℂ) *
              ((Real.sqrt (w j) : ℂ) * (Real.sqrt (w j) : ℂ)) * (u i - u j) := by
          ring
        _ = (Real.sqrt (w i) : ℂ) * (w j : ℂ) * (u i - u j) := by
          rw [show (Real.sqrt (w j) : ℂ) * (Real.sqrt (w j) : ℂ) = (w j : ℂ) by
            norm_cast
            exact Real.mul_self_sqrt (hw j)]
    _ = ((Real.sqrt (w i) : ℝ) : ℂ) *
        (((∑ j, w j : ℝ) : ℂ) * u i - ∑ j, (w j : ℂ) * u j) := by
      calc
        (∑ j, ((Real.sqrt (w i) * w j : ℝ) : ℂ) * (u i - u j)) =
            (Real.sqrt (w i) : ℂ) * ∑ j, (w j : ℂ) * (u i - u j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          push_cast
          ring
        _ = (Real.sqrt (w i) : ℂ) *
            (((∑ j, w j : ℝ) : ℂ) * u i - ∑ j, (w j : ℂ) * u j) := by
          congr 1
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
          push_cast
          rfl

theorem sum_weighted_complex_centered_norm_sq
    {n : ℕ} (w : Fin n → ℝ) (u : Fin n → ℂ) :
    (∑ i, w i *
      ‖((finiteWeightMass w : ℝ) : ℂ) * u i - finiteWeightedMean w u‖ ^ (2 : ℕ)) =
      finiteWeightMass w *
        (finiteWeightMass w * finiteWeightedNormSq w u -
          ‖finiteWeightedMean w u‖ ^ (2 : ℕ)) := by
  have hre := sum_weighted_centered_sq w (fun i => (u i).re)
  have him := sum_weighted_centered_sq w (fun i => (u i).im)
  have hmeanRe : (finiteWeightedMean w u).re = ∑ i, w i * (u i).re := by
    simp [finiteWeightedMean]
  have hmeanIm : (finiteWeightedMean w u).im = ∑ i, w i * (u i).im := by
    simp [finiteWeightedMean]
  have hreMul :
      (∑ i, w i * (((∑ j, w j) * (u i).re - ∑ j, w j * (u j).re) *
        ((∑ j, w j) * (u i).re - ∑ j, w j * (u j).re))) =
        (∑ i, w i) *
          ((∑ i, w i) * ∑ i, w i * ((u i).re * (u i).re) -
            (∑ i, w i * (u i).re) * ∑ i, w i * (u i).re) := by
    simpa only [pow_two] using hre
  have himMul :
      (∑ i, w i * (((∑ j, w j) * (u i).im - ∑ j, w j * (u j).im) *
        ((∑ j, w j) * (u i).im - ∑ j, w j * (u j).im))) =
        (∑ i, w i) *
          ((∑ i, w i) * ∑ i, w i * ((u i).im * (u i).im) -
            (∑ i, w i * (u i).im) * ∑ i, w i * (u i).im) := by
    simpa only [pow_two] using him
  unfold finiteWeightMass finiteWeightedNormSq
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero, mul_add, Finset.sum_add_distrib]
  rw [hmeanRe, hmeanIm]
  rw [hreMul, himMul]
  ring

/-- Exact extraction of weighted pair energy from the one-particle difference matrix. -/
theorem finiteCoefficientL2Norm_weightedDifference_mulVec_sq
    {n : ℕ} (w : Fin n → ℝ) (u : Fin n → ℂ) (hw : ∀ i, 0 ≤ w i) :
    finiteCoefficientL2Norm
        (finiteMatrixMulVec (finiteWeightedDifferenceMatrix w u)
          (finiteSqrtWeightVector w)) ^ (2 : ℕ) =
      finiteWeightMass w * finiteWeightedDifferenceEnergy w u / 2 := by
  rw [finiteCoefficientL2Norm_sq]
  simp_rw [finiteWeightedDifferenceMatrix_mulVec_sqrtWeight w u hw]
  have hterm : ∀ i : Fin n,
      ‖(Real.sqrt (w i) : ℂ) *
        (((finiteWeightMass w : ℝ) : ℂ) * u i - finiteWeightedMean w u)‖ ^ (2 : ℕ) =
      w i * ‖((finiteWeightMass w : ℝ) : ℂ) * u i - finiteWeightedMean w u‖ ^ (2 : ℕ) := by
    intro i
    rw [norm_mul, mul_pow]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw i)]
  simp_rw [hterm]
  rw [sum_weighted_complex_centered_norm_sq]
  rw [finiteWeightedDifferenceEnergy_eq_variance]
  ring

/-- **Weighted difference energy survives every compact perturbation.**  Common Sonin shells
compress the full pair energy with no loss depending on the number of primes. -/
theorem sqrt_half_finiteWeightedDifferenceEnergy_le_norm_primeGram_sub_compact
    {n : ℕ} [Nonempty (Fin n)] (a : ℝ) (ha : 0 < a)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (w : Fin n → ℝ) (u : Fin n → ℂ) (hw : ∀ i, 0 ≤ w i)
    (hmass : 0 < finiteWeightMass w)
    (K : evenSubspace →L[ℂ] evenSubspace) (hK : IsCompactOperator K) :
    Real.sqrt (finiteWeightedDifferenceEnergy w u / 2) ≤
      ‖finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp) (finiteWeightedDifferenceMatrix w u) - K‖ := by
  let x : Fin n → ℂ := finiteSqrtWeightVector w
  let y : Fin n → ℂ := finiteMatrixMulVec (finiteWeightedDifferenceMatrix w u) x
  let T : evenSubspace →L[ℂ] evenSubspace :=
    finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
      (real_prime_one_lt p hp) (finiteWeightedDifferenceMatrix w u)
  have hcompression :=
    finiteCoefficientL2Norm_matrixMulVec_le_norm_finitePrimeEvenDilationGram_sub_compact
      a ha p hp hinj (finiteWeightedDifferenceMatrix w u)
        (finiteWeightedDifferenceMatrix_diagonal w u) x K hK
  have hxSq : finiteCoefficientL2Norm x ^ (2 : ℕ) = finiteWeightMass w := by
    simpa [x] using finiteCoefficientL2Norm_finiteSqrtWeightVector_sq w hw
  have hySq : finiteCoefficientL2Norm y ^ (2 : ℕ) =
      finiteWeightMass w * finiteWeightedDifferenceEnergy w u / 2 := by
    simpa [x, y] using finiteCoefficientL2Norm_weightedDifference_mulVec_sq w u hw
  have hyNonneg : 0 ≤ finiteCoefficientL2Norm y := finiteCoefficientL2Norm_nonneg y
  have hxNonneg : 0 ≤ finiteCoefficientL2Norm x := finiteCoefficientL2Norm_nonneg x
  have hnormNonneg : 0 ≤ ‖T - K‖ := ContinuousLinearMap.opNorm_nonneg (T - K)
  have hsquared : finiteCoefficientL2Norm y ^ (2 : ℕ) ≤
      (finiteCoefficientL2Norm x * ‖T - K‖) ^ (2 : ℕ) :=
    (sq_le_sq₀ hyNonneg (mul_nonneg hxNonneg hnormNonneg)).2 (by
      simpa [x, y, T] using hcompression)
  have henergy : finiteWeightedDifferenceEnergy w u / 2 ≤ ‖T - K‖ ^ (2 : ℕ) := by
    rw [mul_pow, hxSq, hySq] at hsquared
    nlinarith
  rw [Real.sqrt_le_iff]
  exact ⟨hnormNonneg, by simpa [T] using henergy⟩

/-- Reciprocal-prime weights on a finite enumerated prime packet. -/
def finitePrimeReciprocalWeight {n : ℕ} (p : Fin n → ℕ) : Fin n → ℝ :=
  fun i => (p i : ℝ)⁻¹

theorem finitePrimeReciprocalWeight_pos
    {n : ℕ} (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (i : Fin n) :
    0 < finitePrimeReciprocalWeight p i := by
  exact inv_pos.mpr (zero_lt_one.trans (real_prime_one_lt p hp i))

theorem finitePrimeReciprocalWeight_mass_pos
    {n : ℕ} [Nonempty (Fin n)] (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) :
    0 < finiteWeightMass (finitePrimeReciprocalWeight p) := by
  unfold finiteWeightMass
  exact Finset.sum_pos (fun i hi => finitePrimeReciprocalWeight_pos p hp i)
    Finset.univ_nonempty

/-- **Reciprocal-prime seam lower bound.**  The square root of one half of the ordered
reciprocal-prime pair energy is a lower bound for every compactly perturbed Sonin Gram
coboundary. -/
theorem sqrt_half_finitePrimeDifferenceEnergy_le_norm_primeGram_sub_compact
    {n : ℕ} [Nonempty (Fin n)] (a : ℝ) (ha : 0 < a)
    (p : Fin n → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (u : Fin n → ℂ) (K : evenSubspace →L[ℂ] evenSubspace)
    (hK : IsCompactOperator K) :
    Real.sqrt
        (finiteWeightedDifferenceEnergy (finitePrimeReciprocalWeight p) u / 2) ≤
      ‖finiteEvenDilationGramCombination a (fun i => (p i : ℝ))
          (real_prime_one_lt p hp)
          (finiteWeightedDifferenceMatrix (finitePrimeReciprocalWeight p) u) - K‖ := by
  exact sqrt_half_finiteWeightedDifferenceEnergy_le_norm_primeGram_sub_compact
    a ha p hp hinj (finitePrimeReciprocalWeight p) u
      (fun i => (finitePrimeReciprocalWeight_pos p hp i).le)
      (finitePrimeReciprocalWeight_mass_pos p hp) K hK

end RHTower
