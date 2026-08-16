import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallAtomicFredholmLimit
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaPhysicalStokesHellingerBalancedWallSquare
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.HTGeometry.HochsterStrandGeneralBoundary
import GaloisForLFunctions.HTGeometry.CofinalSubsetTsum

/-!
# SP-E exponential-wall Fredholm real-zero closure

The normalized finite Stokes child determinant has the complete ordered-tuple Fredholm expansion,
including repeated prime labels (which vanish only through the literal determinant). Cofinal finite
prime carriers converge to the wall entire determinant. The balanced physical determinant factors
as the product of the normalized child at opposite spectral parameters. Its unconditional real-zero
law therefore passes first to every positive aperture and then, by locally uniform Hurwitz transfer,
to the exponential-wall Fredholm determinant.

This closes the source-side real-rootedness gate. It does not identify the exponential-wall divisor
with Xi and inserts no Xi coefficient, zero, or fitted counterterm.
-/

open Complex Matrix Filter Topology Set MeasureTheory
open scoped BigOperators Matrix


namespace RHTower

noncomputable section

def routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock (d : ℝ) (t : Finset Nat.Primes) :
    Matrix t t ℂ :=
  (((gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℝ) : ℂ)⁻¹) •
    HilbertSchmidt.blockMatrix
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t

def routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet
    (d : ℝ) (t : Finset Nat.Primes) (z : ℂ) : ℂ :=
  (1 + z • routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t).det

theorem routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock_apply
    {d : ℝ} (hd : 0 < d) (t : Finset Nat.Primes) (p q : t) :
    routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t p q =
      ((Real.sqrt (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p) *
        Real.sqrt (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d q) *
        routePPrimitiveGammaJuliaStokesWallCubicKernel
          (Real.log (p : ℝ)) (Real.log (q : ℝ)) : ℝ) : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock, Matrix.smul_apply,
    HilbertSchmidt.blockMatrix,
    routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_wallCubicKernel hd]
  simp only [routePPrimitiveGammaJuliaStokesWallNormalizedWeight]
  have hW : 0 < gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d :=
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  rw [Real.sqrt_div
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd p),
    Real.sqrt_div
      (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_nonneg hd q)]
  norm_cast
  field_simp [hW.ne', (Real.sqrt_pos.2 hW).ne']
  rw [Real.sq_sqrt hW.le]
  rw [Complex.real_smul]
  push_cast
  ring

theorem det_routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock_submatrix_eq_primeFredholm
    {d : ℝ} (hd : 0 < d) (t : Finset Nat.Primes) (n : ℕ)
    (a : Fin n → t) :
    ((routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t).submatrix a a).det =
      (∏ i : Fin n,
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) *
        routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n
          (fun i => (a i : Nat.Primes)) := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i =>
    (Real.sqrt
      (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) : ℂ)
  let A : Matrix (Fin n) (Fin n) ℂ :=
    routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n
      (fun i => (a i : Nat.Primes))
  have hmatrix :
      (routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t).submatrix a a = D * A * D := by
    ext i j
    rw [Matrix.submatrix_apply, routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock_apply hd]
    dsimp [D, A]
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [
      routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul]
  simp only [D, Matrix.det_diagonal,
    routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand, A]
  have hprod :
      (∏ i : Fin n,
          (Real.sqrt
            (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) : ℂ)) *
        (∏ i : Fin n,
          (Real.sqrt
            (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) : ℂ)) =
      ((∏ i : Fin n,
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i) : ℝ) : ℂ) := by
    rw [← Finset.prod_mul_distrib]
    norm_cast
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.mul_self_sqrt (wallNormalizedWeight_nonneg hd (a i))
  calc
    (∏ i : Fin n,
        (Real.sqrt
          (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) : ℂ)) *
          (routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n
            (fun i => (a i : Nat.Primes))).det *
        (∏ i : Fin n,
          (Real.sqrt
            (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) : ℂ)) =
        ((∏ i : Fin n,
          (Real.sqrt
            (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) : ℂ)) *
        (∏ i : Fin n,
          (Real.sqrt
            (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) : ℂ))) *
          (routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n
            (fun i => (a i : Nat.Primes))).det := by ring
    _ = _ := by rw [hprod]

def routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm
    (d : ℝ) (n : ℕ) (a : Fin n → Nat.Primes) : ℂ :=
  (∏ i : Fin n,
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) *
    routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a

theorem summable_norm_routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    Summable (fun a : Fin n → Nat.Primes =>
      ‖routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n a‖) := by
  have hmass : Summable (fun a : Fin n → Nat.Primes =>
      ∏ i : Fin n,
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) := by
    have h := ENNReal.summable_toReal
      (routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).tsum_coe_ne_top
    exact h.congr (fun a =>
      routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF_toReal hd n a)
  refine ((hmass.mul_left ((Real.sqrt n) ^ n)).of_norm_bounded ?_)
  intro a
  rw [norm_norm, routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg fun i hi =>
      wallNormalizedWeight_nonneg hd (a i))]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (norm_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand_le n a)
      (Finset.prod_nonneg fun i hi => wallNormalizedWeight_nonneg hd (a i))

def routePPrimitiveGammaJuliaStokesPrimeTupleSubtypeEquiv (n : ℕ) (t : Finset Nat.Primes) :
    (Fin n → t) ≃
      {a : Fin n → Nat.Primes // ∀ i, a i ∈ t} where
  toFun a := ⟨fun i => a i, fun i => (a i).property⟩
  invFun a i := ⟨a.val i, a.property i⟩
  left_inv a := rfl
  right_inv a := by
    apply Subtype.ext
    rfl

theorem sum_routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm_subtype_eq
    (d : ℝ) (n : ℕ) (t : Finset Nat.Primes) :
    (∑ a : Fin n → t,
      routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n (fun i => (a i : Nat.Primes))) =
      ∑' a : {a : Fin n → Nat.Primes // ∀ i, a i ∈ t},
        routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n a.val := by
  rw [← (routePPrimitiveGammaJuliaStokesPrimeTupleSubtypeEquiv n t).tsum_eq
    (fun a : {a : Fin n → Nat.Primes // ∀ i, a i ∈ t} =>
      routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n a.val)]
  exact (hasSum_fintype (fun a : Fin n → t =>
    routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n (fun i => (a i : Nat.Primes)))).tsum_eq.symm

theorem tendsto_sum_routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    Tendsto
      (fun t : Finset Nat.Primes =>
        ∑ a : Fin n → t,
          routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n (fun i => (a i : Nat.Primes)))
      atTop
      (𝓝 (∑' a : Fin n → Nat.Primes,
        routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n a)) := by
  let A : Finset Nat.Primes → Set (Fin n → Nat.Primes) :=
    fun t => {a | ∀ i, a i ∈ t}
  have hcof : ∀ F : Finset (Fin n → Nat.Primes),
      ∀ᶠ t : Finset Nat.Primes in atTop, (F : Set (Fin n → Nat.Primes)) ⊆ A t := by
    intro F
    let U : Finset Nat.Primes :=
      F.biUnion fun a => Finset.image a Finset.univ
    filter_upwards [eventually_ge_atTop U] with t ht
    intro a ha i
    exact ht (Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
  have h := HTGeometry.tendsto_tsum_subtype_of_cofinal
    (f := routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n)
    (A := A)
    (summable_norm_routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm hd n) hcof
  apply h.congr'
  filter_upwards [] with t
  change (∑' a : {a : Fin n → Nat.Primes // ∀ i, a i ∈ t},
      routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n a.val) =
    ∑ a : Fin n → t,
      routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n (fun i => (a i : Nat.Primes))
  exact (sum_routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm_subtype_eq d n t).symm

theorem sum_routePPrimitiveGammaJuliaStokesWallNormalizedWeight_product_le_one
    {d : ℝ} (hd : 0 < d) (t : Finset Nat.Primes) (n : ℕ) :
    (∑ a : Fin n → t, ∏ i : Fin n,
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) ≤ 1 := by
  let f : t → ℝ := fun p =>
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p
  change (∑ a : Fin n → t, ∏ i : Fin n, f (a i)) ≤ 1
  rw [← Fintype.sum_pow f n]
  have hpartial :
      (∑ p : t,
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p) ≤ 1 := by
    have h := (summable_wallNormalizedWeight hd).sum_le_tsum t
      (fun p hp => wallNormalizedWeight_nonneg hd p)
    rw [tsum_wallNormalizedWeight hd] at h
    calc
      (∑ p : t,
          routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p) =
          ∑ p ∈ t,
            routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p :=
        by
          simpa only [Finset.attach_eq_univ] using
            (Finset.sum_attach t
              (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d))
      _ ≤ 1 := h
  have hnonneg : 0 ≤ ∑ p : t,
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p :=
    Finset.sum_nonneg fun p hp => wallNormalizedWeight_nonneg hd p
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using pow_le_one₀ hnonneg hpartial

theorem finiteFredholm_det_submatrix_eq_zero_of_not_injective
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (M : Matrix ι ι ℂ) {n : ℕ} (a : Fin n → ι)
    (ha : ¬ Function.Injective a) :
    (M.submatrix a a).det = 0 := by
  rw [Function.not_injective_iff] at ha
  obtain ⟨i, j, haij, hij⟩ := ha
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp only [Matrix.submatrix_apply]
  rw [haij]

theorem finiteFredholm_det_submatrix_comp_perm
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (M : Matrix ι ι ℂ) {n : ℕ} (a : Fin n → ι)
    (σ : Equiv.Perm (Fin n)) :
    (M.submatrix (a ∘ σ) (a ∘ σ)).det =
      (M.submatrix a a).det := by
  simpa [Matrix.submatrix, Function.comp_def] using
    Matrix.det_submatrix_equiv_self σ (M.submatrix a a)

theorem finiteFredholm_sum_det_submatrix_fiber
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (M : Matrix ι ι ℂ) {n : ℕ} (s : Finset ι) (hs : s.card = n) :
    (∑ a : Fin n → ι with
        Function.Injective a ∧ Finset.image a Finset.univ = s,
        (M.submatrix a a).det) =
      (n.factorial : ℂ) *
        (M.submatrix (s.orderEmbOfFin hs) (s.orderEmbOfFin hs)).det := by
  classical
  let e : Fin n → ι := s.orderEmbOfFin hs
  have he : Function.Injective e := (s.orderEmbOfFin hs).injective
  rw [show (n.factorial : ℂ) =
      ∑ _σ : Equiv.Perm (Fin n), (1 : ℂ) by
    simp [Fintype.card_perm]]
  rw [Finset.sum_mul]
  symm
  refine Finset.sum_bij
      (s := Finset.univ)
      (t := Finset.univ.filter (fun a : Fin n → ι =>
        Function.Injective a ∧ Finset.image a Finset.univ = s))
      (f := fun _σ : Equiv.Perm (Fin n) =>
        (1 : ℂ) * (M.submatrix (s.orderEmbOfFin hs) (s.orderEmbOfFin hs)).det)
      (g := fun a : Fin n → ι => (M.submatrix a a).det)
      (fun σ _hσ => e ∘ σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact he.comp σ.injective
    · rw [Finset.image_comp]
      rw [Finset.image_univ_equiv]
      exact Finset.image_orderEmbOfFin_univ s hs
  · intro σ₁ hσ₁ σ₂ hσ₂ h
    apply Equiv.ext
    intro i
    exact he (congrFun h i)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    have hmem : ∀ t : Fin n, ∃ j : Fin n, a j = e t := by
      intro t
      have het : e t ∈ s := by
        simp [e]
      rw [← ha.2] at het
      simpa only [Finset.mem_image, Finset.mem_univ, true_and] using het
    obtain ⟨π, hπ⟩ :=
      GaloisForLFunctions.HTGeometry.exists_perm_comp_of_mem he hmem
    refine ⟨π.symm, Finset.mem_univ _, ?_⟩
    funext i
    have hi := congrFun hπ (π.symm i)
    simpa [Function.comp_def] using hi.symm
  · intro σ hσ
    simpa [e, one_mul] using
      (finiteFredholm_det_submatrix_comp_perm M e σ).symm

theorem finiteFredholm_sum_det_submatrix_eq_factorial_mul_sum_minors
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (M : Matrix ι ι ℂ) (n : ℕ) :
    (∑ a : Fin n → ι, (M.submatrix a a).det) =
      (n.factorial : ℂ) *
        ∑ s ∈ Finset.powersetCard n Finset.univ,
          (M.submatrix Subtype.val Subtype.val : Matrix s s ℂ).det := by
  classical
  have hfilter :
      (∑ a : Fin n → ι, (M.submatrix a a).det) =
        ∑ a : Fin n → ι with Function.Injective a,
          (M.submatrix a a).det := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ha ha'
    have hnot : ¬ Function.Injective a := by
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha'
    exact finiteFredholm_det_submatrix_eq_zero_of_not_injective M a hnot
  rw [hfilter]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun a : Fin n → ι => Function.Injective a))
    (t := Finset.powersetCard n Finset.univ)
    (g := fun a => Finset.image a Finset.univ)
    (f := fun a => (M.submatrix a a).det)]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hscard : s.card = n := (Finset.mem_powersetCard.mp hs).2
    rw [show (∑ a ∈ Finset.univ.filter
          (fun a : Fin n → ι => Function.Injective a) with
          Finset.image a Finset.univ = s,
          (M.submatrix a a).det) =
        ∑ a : Fin n → ι with
          Function.Injective a ∧ Finset.image a Finset.univ = s,
          (M.submatrix a a).det by
      apply Finset.sum_congr
      · ext a
        simp [and_comm]
      · intro a ha
        rfl]
    rw [finiteFredholm_sum_det_submatrix_fiber M s hscard]
    congr 1
    simpa [Matrix.submatrix, Finset.coe_orderIsoOfFin_apply] using
      Matrix.det_submatrix_equiv_self (s.orderIsoOfFin hscard).toEquiv
        (M.submatrix (fun x : s => (x : ι)) (fun x : s => (x : ι)))
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_powersetCard]
    constructor
    · exact Finset.subset_univ _
    · rw [Finset.card_image_iff.mpr ha.2.injOn, Finset.card_univ,
        Fintype.card_fin]

theorem finiteFredholm_coeff_det_one_add_X_smul_eq_ordered_tuples
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (M : Matrix ι ι ℂ) (n : ℕ) :
    (1 + (Polynomial.X : Polynomial ℂ) •
      M.map (Polynomial.C : ℂ → Polynomial ℂ)).det.coeff n =
      (∑ a : Fin n → ι, (M.submatrix a a).det) / (n.factorial : ℂ) := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    finiteFredholm_sum_det_submatrix_eq_factorial_mul_sum_minors]
  have hn : (n.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hn]

theorem finiteFredholm_det_one_add_smul_eq_ordered_tuple_tsum
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    (M : Matrix ι ι ℂ) (z : ℂ) :
    (1 + z • M).det =
      ∑' n : ℕ, z ^ n *
        ((∑ a : Fin n → ι, (M.submatrix a a).det) /
          (n.factorial : ℂ)) := by
  let P : Polynomial ℂ :=
    (1 + (Polynomial.X : Polynomial ℂ) •
      M.map (Polynomial.C : ℂ → Polynomial ℂ)).det
  have hcoeff : ∀ n : ℕ,
      (∑ a : Fin n → ι, (M.submatrix a a).det) / (n.factorial : ℂ) =
        P.coeff n := by
    intro n
    exact (finiteFredholm_coeff_det_one_add_X_smul_eq_ordered_tuples M n).symm
  rw [show (∑' n : ℕ, z ^ n *
        ((∑ a : Fin n → ι, (M.submatrix a a).det) /
          (n.factorial : ℂ))) =
      ∑' n : ℕ, z ^ n * P.coeff n by
    congr 1
    funext n
    rw [hcoeff n]]
  rw [tsum_eq_sum (s := P.support) (fun n hn => by
    have hn0 : P.coeff n = 0 := by
      simpa [Polynomial.mem_support_iff] using hn
    rw [hn0, mul_zero])]
  have heval : P.eval z = (1 + z • M).det := by
    change (Polynomial.evalRingHom z)
        ((1 + (Polynomial.X : Polynomial ℂ) •
          M.map (Polynomial.C : ℂ → Polynomial ℂ)).det) = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij] <;> ring
  rw [← heval, Polynomial.eval_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem finiteFredholm_det_one_add_smul_eq_ordered_tuple_tsum_fintype
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (z : ℂ) :
    (1 + z • M).det =
      ∑' n : ℕ, z ^ n *
        ((∑ a : Fin n → ι, (M.submatrix a a).det) /
          (n.factorial : ℂ)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let MF : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
    Matrix.reindex e e M
  have hfin := finiteFredholm_det_one_add_smul_eq_ordered_tuple_tsum MF z
  have hleft : (1 + z • MF).det = (1 + z • M).det := by
    have hreindex : Matrix.reindex e e (1 + z • M) = 1 + z • MF := by
      ext i j
      simp [MF, Matrix.one_apply]
    rw [← hreindex, Matrix.det_reindex_self]
  have hsum (n : ℕ) :
      (∑ b : Fin n → Fin (Fintype.card ι), (MF.submatrix b b).det) =
        ∑ a : Fin n → ι, (M.submatrix a a).det := by
    let E : (Fin n → ι) ≃ (Fin n → Fin (Fintype.card ι)) :=
      Equiv.piCongrRight (fun _ => e)
    symm
    refine Fintype.sum_equiv E _ _ ?_
    intro a
    congr 1
    ext i j
    simp [E, MF, Matrix.submatrix_apply, e]
  rw [hleft] at hfin
  simpa only [hsum] using hfin

set_option maxHeartbeats 800000 in
theorem routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet_eq_orderedTuple_tsum
    {d : ℝ} (hd : 0 < d) (t : Finset Nat.Primes) (z : ℂ) :
    routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet d t z =
      ∑' n : ℕ, z ^ n *
        ((∑ a : Fin n → t,
          routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n
            (fun i => (a i : Nat.Primes))) / (n.factorial : ℂ)) := by
  unfold routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet
  have hdet := finiteFredholm_det_one_add_smul_eq_ordered_tuple_tsum_fintype
    (routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t) z
  calc
    (1 + z • routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t).det =
        ∑' n : ℕ, z ^ n *
          ((∑ a : Fin n → t,
            ((routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t).submatrix a a).det) /
            (n.factorial : ℂ)) := hdet
    _ = _ := by
      apply tsum_congr
      intro n
      congr 1
      congr 1
      apply Fintype.sum_congr
      intro a
      exact det_routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock_submatrix_eq_primeFredholm hd t n a

theorem norm_routePPrimitiveGammaJuliaStokesFiniteNormalizedAtomicCoefficient_le
    {d : ℝ} (hd : 0 < d) (t : Finset Nat.Primes) (n : ℕ) :
    ‖((∑ a : Fin n → t,
        routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n
          (fun i => (a i : Nat.Primes))) / (n.factorial : ℂ))‖ ≤
      (Real.sqrt n) ^ n / (n.factorial : ℝ) := by
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n.factorial)
  calc
    ‖∑ a : Fin n → t,
        routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n
          (fun i => (a i : Nat.Primes))‖ ≤
        ∑ a : Fin n → t,
          ‖routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n
            (fun i => (a i : Nat.Primes))‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin n → t,
          (∏ i : Fin n,
            routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) *
              (Real.sqrt n) ^ n := by
      apply Finset.sum_le_sum
      intro a ha
      rw [routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i hi =>
          wallNormalizedWeight_nonneg hd (a i))]
      exact mul_le_mul_of_nonneg_left
        (norm_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand_le n
          (fun i => (a i : Nat.Primes)))
        (Finset.prod_nonneg fun i hi => wallNormalizedWeight_nonneg hd (a i))
    _ = (∑ a : Fin n → t,
          ∏ i : Fin n,
            routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) *
              (Real.sqrt n) ^ n := by
      rw [Finset.sum_mul]
    _ ≤ 1 * (Real.sqrt n) ^ n := by
      gcongr
      exact sum_routePPrimitiveGammaJuliaStokesWallNormalizedWeight_product_le_one hd t n
    _ = (Real.sqrt n) ^ n := one_mul _

set_option maxHeartbeats 800000 in
theorem tendsto_routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet
    {d : ℝ} (hd : 0 < d) (z : ℂ) :
    Tendsto
      (fun t : Finset Nat.Primes => routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet d t z)
      atTop
      (𝓝 (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z)) := by
  have hseries : Tendsto
      (fun t : Finset Nat.Primes =>
        ∑' n : ℕ, z ^ n *
          ((∑ a : Fin n → t,
            routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n
              (fun i => (a i : Nat.Primes))) / (n.factorial : ℂ)))
      atTop
      (𝓝 (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z)) := by
    unfold routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
    apply tendsto_tsum_of_dominated_convergence
      (ContinuousKernelFredholm.summable_hadamard_majorant ‖z‖ (norm_nonneg z))
    · intro n
      have hn := (tendsto_sum_routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm hd n).div_const
        (n.factorial : ℂ)
      have hcoeff :=
        routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_eq_orderedPrimeTuple_tsum
          hd n
      exact tendsto_const_nhds.mul
        (by simpa [hcoeff, routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm] using hn)
    · exact Filter.Eventually.of_forall fun t n => by
        rw [norm_mul, norm_pow]
        calc
          ‖z‖ ^ n *
              ‖(∑ a : Fin n → t,
                routePPrimitiveGammaJuliaStokesWallAtomicFredholmTerm d n
                  (fun i => (a i : Nat.Primes))) / (n.factorial : ℂ)‖ ≤
              ‖z‖ ^ n * ((Real.sqrt n) ^ n / (n.factorial : ℝ)) := by
            gcongr
            exact norm_routePPrimitiveGammaJuliaStokesFiniteNormalizedAtomicCoefficient_le hd t n
          _ = (Real.sqrt n * ‖z‖) ^ n / (n.factorial : ℝ) := by ring
  apply hseries.congr'
  filter_upwards [] with t
  exact (routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet_eq_orderedTuple_tsum hd t z).symm

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteDet_scaled_eq_normalizedChild_prod
    {d : ℝ} (hd : 0 < d) (t : Finset Nat.Primes) (z : ℂ) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
        (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t)
        (z / (8 *
          (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))) =
      routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet d t z *
        routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet d t (-z) := by
  rw [
    routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet_eq_squaredChild]
  unfold routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet
  rw [← Matrix.det_mul]
  let H : Matrix t t ℂ :=
    HilbertSchmidt.blockMatrix
      (routePPrimitiveGammaJuliaStokesCofinalChildKernel d) t
  let W : ℂ :=
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ)
  have hW : W ≠ 0 := by
    dsimp [W]
    exact Complex.ofReal_ne_zero.mpr
      (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'
  have hfactor :
      (1 + z • routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t) *
          (1 + (-z) • routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t) =
        1 - (z ^ 2) •
          (routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t * routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock d t) := by
    simp [mul_add, add_mul, smul_smul]
    rw [pow_two]
    abel
  rw [hfactor]
  congr 1
  ext i j
  simp only [routePPrimitiveGammaJuliaPhysicalStokesHellingerSquaredChildPencil,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  simp only [routePPrimitiveGammaJuliaStokesNormalizedChildFiniteBlock]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp only [Matrix.smul_apply]
  field_simp [hW]
  ring

theorem routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_scaled_eq_wallFredholmEntireDet_prod
    {d : ℝ} (hd : 0 < d) (z : ℂ) :
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d 1
        (z / (8 *
          (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))) =
      routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z *
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) (-z) := by
  let u : ℂ := z / (8 *
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))
  have hphys :=
    tendsto_routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelCompleteFiniteDet hd u
  have hprod :=
    (tendsto_routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet hd z).mul
      (tendsto_routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet hd (-z))
  have hstage :
      (fun t : Finset Nat.Primes =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryFiniteDet d 1
          (routePPrimitiveGammaJuliaPhysicalStokesHellingerChannelComplete t) u) =
      (fun t : Finset Nat.Primes =>
        routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet d t z *
          routePPrimitiveGammaJuliaStokesNormalizedChildFiniteDet d t (-z)) := by
    funext t
    exact routePPrimitiveGammaJuliaPhysicalStokesHellingerFiniteDet_scaled_eq_normalizedChild_prod hd t z
  rw [hstage] at hphys
  exact tendsto_nhds_unique hphys hprod

theorem routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero_im_eq_zero
    {d : ℝ} (hd : 0 < d) {z : ℂ}
    (hz : routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z = 0) :
    z.im = 0 := by
  have hbridge :=
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_scaled_eq_wallFredholmEntireDet_prod hd z
  have hphysical :
      routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet d 1
        (z / (8 *
          (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ))) = 0 := by
    rw [hbridge, hz, zero_mul]
  have him :=
    routePPrimitive_GammaJulia_physicalStokesHellingerOrdinaryDeterminant
      d hd 1 (by norm_num) |>.2.2.2.1 _ hphysical
  have hWpos : 0 < gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d :=
    gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  let c : ℝ := 8 * gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  have hscale :
      (8 * (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d : ℂ)) =
        (c : ℂ) := by
    dsimp [c]
    push_cast
    rfl
  rw [hscale] at him
  have hzrepr : z = (z / (c : ℂ)) * (c : ℂ) := by
    field_simp [hc]
  have himrepr := congrArg Complex.im hzrepr
  simpa [Complex.mul_im, him] using himrepr

def routePPrimitiveGammaJuliaStokesCanonicalApertureSequence (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

theorem routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos (n : ℕ) :
    0 < routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n := by
  unfold routePPrimitiveGammaJuliaStokesCanonicalApertureSequence
  positivity

theorem tendsto_routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_nhdsGT_zero :
    Tendsto routePPrimitiveGammaJuliaStokesCanonicalApertureSequence atTop (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Filter.Eventually.of_forall routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos⟩

theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_apertureSequence :
    TendstoLocallyUniformly
      (fun n z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)) z)
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (ProbabilityTheory.expMeasure 1))
      atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let rho : ℝ := |R| + 1
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hKRho : K ⊆ Metric.closedBall (0 : ℂ) rho :=
    hKR.trans (Metric.closedBall_subset_closedBall (by
      dsimp [rho]
      linarith [le_abs_self R]))
  have hball :=
    tendstoUniformlyOn_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_nhdsGT_zero
      hrho
  have hseqBall : TendstoUniformlyOn
      (fun n z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)) z)
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (ProbabilityTheory.expMeasure 1))
      atTop (Metric.closedBall 0 rho) := fun U hU =>
    tendsto_routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_nhdsGT_zero.eventually (hball U hU)
  exact hseqBall.mono hKRho

theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_partialSum
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (hsupp : mu (Iio 0) = 0) :
    TendstoLocallyUniformly
      (fun N z => ∑ n ∈ Finset.range N,
        z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient mu n)
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet mu)
      atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let rho : ℝ := |R| + 1
  have hrho : 0 ≤ rho := by
    dsimp [rho]
    positivity
  have hKRho : K ⊆ Metric.closedBall (0 : ℂ) rho :=
    hKR.trans (Metric.closedBall_subset_closedBall (by
      dsimp [rho]
      linarith [le_abs_self R]))
  have hball : TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ =>
        ∑ n ∈ Finset.range N,
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient mu n)
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet mu)
      atTop (Metric.closedBall 0 rho) := by
    change TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ =>
        ∑ n ∈ Finset.range N,
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient mu n)
      (fun z : ℂ => ∑' n : ℕ,
        z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient mu n)
      atTop (Metric.closedBall 0 rho)
    exact tendstoUniformlyOn_tsum_nat
      (summable_routePPrimitiveGammaJuliaStokesWallFredholmMajorant hrho)
      (s := Metric.closedBall (0 : ℂ) rho)
      (f := fun (n : ℕ) (z : ℂ) =>
        z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient mu n)
      (fun n z hz =>
        norm_routePPrimitiveGammaJuliaStokesWallFredholmTerm_le_majorant
          mu hsupp hrho hz n)
  exact hball.mono hKRho

theorem differentiable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
    (mu : Measure ℝ) [IsProbabilityMeasure mu] (hsupp : mu (Iio 0) = 0) :
    Differentiable ℂ
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet mu) := by
  have hlocal :=
    tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_partialSum mu hsupp
  have hdiff : ∀ᶠ N : ℕ in atTop,
      DifferentiableOn ℂ
        (fun z : ℂ => ∑ n ∈ Finset.range N,
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient mu n)
        Set.univ := by
    exact Filter.Eventually.of_forall fun N => by
      intro z hz
      fun_prop
  exact differentiableOn_univ.mp
    (hlocal.tendstoLocallyUniformlyOn.differentiableOn hdiff isOpen_univ)

theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_prod_apertureSequence :
    TendstoLocallyUniformly
      (fun n z =>
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)) z *
          routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)) (-z))
      (fun z =>
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
            (ProbabilityTheory.expMeasure 1) z *
          routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
            (ProbabilityTheory.expMeasure 1) (-z))
      atTop := by
  let D0 : ℂ → ℂ :=
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (ProbabilityTheory.expMeasure 1)
  have hplus :=
    tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_apertureSequence
  have hminus0 := hplus.comp (fun z : ℂ => -z) continuous_neg
  have hminus : TendstoLocallyUniformly
      (fun n z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n)) (-z))
      (fun z => D0 (-z)) atTop := by
    simpa [D0, Function.comp_def] using hminus0
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos
  have hD0diff : Differentiable ℂ D0 := by
    exact differentiable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (ProbabilityTheory.expMeasure 1)
      GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero
  have hD0cont : Continuous D0 := hD0diff.continuous
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  by_cases hne : K.Nonempty
  · have hplusK :=
      (tendstoLocallyUniformly_iff_forall_isCompact.mp hplus) K hK
    have hminusK :=
      (tendstoLocallyUniformly_iff_forall_isCompact.mp hminus) K hK
    have hbddPlus : BddAbove ((fun z : ℂ => ‖D0 z‖) '' K) :=
      hK.bddAbove_image hD0cont.norm.continuousOn
    have hbddMinus : BddAbove ((fun z : ℂ => ‖D0 (-z)‖) '' K) :=
      hK.bddAbove_image
        ((hD0cont.comp continuous_neg).norm.continuousOn)
    simpa [D0] using tendstoUniformlyOn_mul_complex_of_bddAbove
      hplusK hminusK hne hbddPlus hbddMinus
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact fun U hU => Filter.Eventually.of_forall fun n z hz => hz.elim

theorem tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokes_scaledPhysical_apertureSequence :
    TendstoLocallyUniformly
      (fun n z =>
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) 1
          (z / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))))
      (fun z =>
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
            (ProbabilityTheory.expMeasure 1) z *
          routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
            (ProbabilityTheory.expMeasure 1) (-z))
      atTop := by
  apply tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_prod_apertureSequence.congr
  intro n z
  exact (routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_scaled_eq_wallFredholmEntireDet_prod
    (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n) z).symm

theorem routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero (mu : Measure ℝ) :
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet mu 0 = 1 := by
  unfold routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
  rw [tsum_eq_single 0]
  · simp [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient,
      routePPrimitiveGammaJuliaStokesWallFredholmIntegrand]
    simp [Measure.real,
      routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure_apply_univ]
  · intro n hn
    simp [hn]

theorem routePPrimitiveGammaJuliaStokesExpWallFredholmEntireDet_zero_im_eq_zero {z : ℂ}
    (hz : routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (ProbabilityTheory.expMeasure 1) z = 0) :
    z.im = 0 := by
  let D0 : ℂ → ℂ :=
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (ProbabilityTheory.expMeasure 1)
  let F : ℂ → ℂ := fun w => D0 w * D0 (-w)
  let Fn : ℕ → ℂ → ℂ := fun n w =>
    routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
      (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) 1
      (w / (8 *
        (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ)))
  have hconv : TendstoLocallyUniformly Fn F atTop := by
    simpa [Fn, F, D0] using
      tendstoLocallyUniformly_routePPrimitiveGammaJuliaStokes_scaledPhysical_apertureSequence
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos
  have hDdiff : Differentiable ℂ D0 := by
    exact differentiable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (ProbabilityTheory.expMeasure 1)
      GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero
  have hDneg : Differentiable ℂ (fun w : ℂ => D0 (-w)) := by
    simpa [Function.comp_def] using hDdiff.comp differentiable_neg
  have hFdiff : Differentiable ℂ F := by
    change Differentiable ℂ (D0 * fun w : ℂ => D0 (-w))
    exact hDdiff.mul hDneg
  have hFanalytic : AnalyticOnNhd ℂ F Set.univ :=
    hFdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hFnDiff : ∀ᶠ n : ℕ in atTop, Differentiable ℂ (Fn n) := by
    exact Filter.Eventually.of_forall fun n => by
      have houter :=
        differentiable_routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet
          (d := routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) (r := 1)
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n)
      have hinner : Differentiable ℂ (fun w : ℂ =>
          w / (8 *
            (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent
              (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence n) : ℂ))) := by
        fun_prop
      simpa [Fn, Function.comp_def] using houter.comp hinner
  have hzeroFn : ∀ᶠ n : ℕ in atTop, ∀ w, Fn n w = 0 → w.im = 0 := by
    exact Filter.Eventually.of_forall fun n w hw => by
      have hbridge :=
        routePPrimitiveGammaJuliaPhysicalStokesHellingerOrdinaryEntireDet_scaled_eq_wallFredholmEntireDet_prod
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n) w
      dsimp [Fn] at hw
      rw [hbridge] at hw
      rcases mul_eq_zero.mp hw with hplus | hminus
      · exact routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero_im_eq_zero
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n) hplus
      · have hneg := routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero_im_eq_zero
          (routePPrimitiveGammaJuliaStokesCanonicalApertureSequence_pos n) hminus
        simpa using hneg
  have hFzero : F 0 ≠ 0 := by
    dsimp [F, D0]
    simp only [neg_zero]
    rw [routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]
    norm_num
  have hFz : F z = 0 := by
    dsimp [F, D0]
    rw [hz, zero_mul]
  exact zero_mem_closed_of_tendstoLocallyUniformly
    hconv hFanalytic hFnDiff
    (isClosed_eq Complex.continuous_im continuous_const)
    hzeroFn hFzero hFz

end


end RHTower
