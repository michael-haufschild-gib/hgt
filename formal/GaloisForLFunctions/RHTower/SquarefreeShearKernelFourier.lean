import GaloisForLFunctions.RHTower.SquarefreeShearKernelSpectrum
import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse
import GaloisForLFunctions.HTGeometry.AddCharFinset
import GaloisForLFunctions.HTGeometry.DistinctPrimeFamilyCRT

/-!
# Exact Fourier diagonal of the squarefree shear kernel

For a prime `p`, the fixed-gap root density is the actual cardinality of
`r * (r + h) = 0` in `ZMod p`.  Its unnormalized Fourier transform is exactly

`2p 1_(j = 0) - 1`.

For a labelled family of distinct primes, this module transports the literal root density and
Mathlib's standard additive character through the canonical CRT equivalence.  The restrictions of
the global character need not be the naively labelled local standard characters; the proof tracks
the actual restricted additive characters and proves that each is trivial exactly when the
corresponding CRT frequency vanishes.  This yields the exact global identity `(SG5)` with no choice
of CRT unit twists and no surrogate density.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Actual prime quadratic-root density, evaluated at the canonical residue representative. -/
def primeQuadraticRootDensity (p : ℕ) (h : ZMod p) : ℂ :=
  (quadraticCongruenceRootCountTotal p (h.val : ℤ) : ℕ)

/-- Local Fourier diagonal `2p 1_(j = 0) - 1`. -/
def primeShearFourierDiagonal (p : ℕ) (j : ZMod p) : ℂ :=
  2 * p * (if j = 0 then 1 else 0) - 1

/-- At a prime, the reducible quadratic has one root at zero gap and two otherwise. -/
theorem primeQuadraticRootDensity_eq
    {p : ℕ} (hp : p.Prime) (h : ZMod p) :
    primeQuadraticRootDensity p h = if h = 0 then 1 else 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [primeQuadraticRootDensity, quadraticCongruenceRootCountTotal_prime hp]
  have hdiv : (p : ℤ) ∣ (h.val : ℤ) ↔ h = 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [hdiv]
  split_ifs <;> norm_num

/-- Literal Fourier transform of the prime root density against an arbitrary additive character. -/
def primeQuadraticRootDensityAddCharFourier
    (p : ℕ) (hp : p.Prime) (ψ : AddChar (ZMod p) ℂ) : ℂ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact ∑ h : ZMod p, primeQuadraticRootDensity p h * ψ h

/-- The prime root-density transform is `2p - 1` for the trivial character and `-1` for every
nontrivial character. -/
theorem primeQuadraticRootDensity_addChar_fourier
    {p : ℕ} (hp : p.Prime) (ψ : AddChar (ZMod p) ℂ) :
    primeQuadraticRootDensityAddCharFourier p hp ψ =
      2 * p * (if ψ = 1 then 1 else 0) - 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [primeQuadraticRootDensityAddCharFourier]
  simp_rw [primeQuadraticRootDensity_eq hp]
  calc
    (∑ h : ZMod p, (if h = 0 then (1 : ℂ) else 2) * ψ h) =
        ∑ h : ZMod p, (2 * ψ h - if h = 0 then ψ h else 0) := by
      apply Finset.sum_congr rfl
      intro h _
      by_cases hh : h = 0
      · simp [hh]
        norm_num
      · simp [hh]
    _ = (∑ h : ZMod p, 2 * ψ h) -
        ∑ h : ZMod p, if h = 0 then ψ h else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = 2 * (∑ h : ZMod p, ψ h) - 1 := by
      rw [Finset.mul_sum]
      congr 1
      simp
    _ = 2 * p * (if ψ = 1 then 1 else 0) - 1 := by
      by_cases hψ : ψ = 1
      · subst ψ
        simp
      · rw [AddChar.sum_eq_zero_of_ne_one hψ]
        simp [hψ]

/-- Literal standard-character Fourier transform of the prime root density. -/
def primeQuadraticRootDensityFourier
    (p : ℕ) (hp : p.Prime) (j : ZMod p) : ℂ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact ∑ h : ZMod p, primeQuadraticRootDensity p h *
    ZMod.stdAddChar (-(j * h))

/-- Prime case of `(SG5)`. -/
theorem primeQuadraticRootDensity_fourier
    {p : ℕ} (hp : p.Prime) (j : ZMod p) :
    primeQuadraticRootDensityFourier p hp j = primeShearFourierDiagonal p j := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hshift : ZMod.stdAddChar.mulShift (-j) = 1 ↔ j = 0 := by
    constructor
    · intro h
      by_contra hj
      exact ZMod.isPrimitive_stdAddChar p (neg_ne_zero.mpr hj) h
    · intro hj
      subst j
      ext x
      simp [AddChar.mulShift]
  have hmain := primeQuadraticRootDensity_addChar_fourier hp
    (ZMod.stdAddChar.mulShift (-j))
  rw [if_congr hshift rfl rfl] at hmain
  simpa [primeQuadraticRootDensityFourier, primeShearFourierDiagonal,
    primeQuadraticRootDensityAddCharFourier, AddChar.mulShift, mul_comm] using hmain

/-- Existing certified family of pairwise distinct primes, exposed in the shear namespace. -/
abbrev SquarefreePrimeFamily (k : ℕ) :=
  GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily k

/-- Product of local residue rings for a certified squarefree prime family. -/
abbrev squarefreePrimeResidues {k : ℕ} (P : SquarefreePrimeFamily k) :=
  ∀ i, ZMod (P.primeValue i)

/-- Actual composite-modulus root density, transported to CRT coordinates. -/
def squarefreePrimeRootDensity {k : ℕ} (P : SquarefreePrimeFamily k)
    (h : squarefreePrimeResidues P) : ℂ :=
  (quadraticCongruenceRootCountTotal P.product
    ((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).symm h).val : ℕ)

/-- Root counts factor over a certified distinct-prime product. -/
theorem quadraticCongruenceRootCountTotal_primeFamily_prod
    {k : ℕ} (P : SquarefreePrimeFamily k) (h : ℤ) :
    quadraticCongruenceRootCountTotal P.product h =
      ∏ i, quadraticCongruenceRootCountTotal (P.primeValue i) h := by
  let s := Finset.univ.image P.primeValue
  have hpair : (s : Set ℕ).Pairwise Nat.Coprime := by
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨i, _, hia⟩
    rcases Finset.mem_image.mp hb with ⟨j, _, hjb⟩
    have hpa : a.Prime := by simpa [hia] using P.prime i
    have hpb : b.Prime := by simpa [hjb] using P.prime j
    exact (Nat.coprime_primes hpa hpb).mpr hab
  have hnz : ∀ n ∈ s, n ≠ 0 := by
    intro n hn
    simp only [s, Finset.mem_image, Finset.mem_univ, true_and] at hn
    obtain ⟨i, rfl⟩ := hn
    exact (P.prime i).ne_zero
  have hfactor := quadraticCongruenceRootCountTotal_prod s hpair hnz h
  rw [show (∏ n ∈ s, n) = P.product by
    rw [GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.product]
    exact Finset.prod_image P.injective.injOn]
    at hfactor
  rw [show (∏ n ∈ s, quadraticCongruenceRootCountTotal n h) =
      ∏ i, quadraticCongruenceRootCountTotal (P.primeValue i) h by
    exact Finset.prod_image P.injective.injOn]
    at hfactor
  exact hfactor

/-- A canonical global representative reduces to its given CRT coordinate. -/
theorem squarefreePrime_crtEquiv_symm_val_cast
    {k : ℕ} (P : SquarefreePrimeFamily k)
    (h : squarefreePrimeResidues P) (i : Fin k) :
    (((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).symm h).val :
      ZMod (P.primeValue i)) = h i := by
  letI : NeZero (∏ i, P.primeValue i) :=
    ⟨Finset.prod_ne_zero_iff.mpr fun i _ => (P.prime i).ne_zero⟩
  unfold GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv
  unfold GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.product
  have he := congrFun
    ((ZMod.prodEquivPi P.primeValue P.pairwise_coprime).apply_symm_apply h) i
  rw [ZMod.prodEquivPi_apply] at he
  exact (ZMod.natCast_val
    ((ZMod.prodEquivPi P.primeValue P.pairwise_coprime).symm h)).trans he

/-- Local root count computed from a global CRT representative equals the count from the local
canonical representative. -/
theorem quadraticCongruenceRootCountTotal_crtCoordinate
    {k : ℕ} (P : SquarefreePrimeFamily k)
    (h : squarefreePrimeResidues P) (i : Fin k) :
    quadraticCongruenceRootCountTotal (P.primeValue i)
        ((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).symm h).val =
      quadraticCongruenceRootCountTotal (P.primeValue i) (h i).val := by
  letI : NeZero (P.primeValue i) := ⟨(P.prime i).ne_zero⟩
  rw [quadraticCongruenceRootCountTotal_prime (P.prime i),
    quadraticCongruenceRootCountTotal_prime (P.prime i)]
  have hdivLeft :
      ((P.primeValue i : ℕ) : ℤ) ∣
          ((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).symm h).val ↔
        h i = 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_natCast, squarefreePrime_crtEquiv_symm_val_cast]
  have hdivRight : ((P.primeValue i : ℕ) : ℤ) ∣ ((h i).val : ℤ) ↔ h i = 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [hdivLeft, hdivRight]

/-- Composite root density is exactly the tensor product of its actual prime root densities. -/
theorem squarefreePrimeRootDensity_eq_prod
    {k : ℕ} (P : SquarefreePrimeFamily k) (h : squarefreePrimeResidues P) :
    squarefreePrimeRootDensity P h =
      ∏ i, primeQuadraticRootDensity (P.primeValue i) (h i) := by
  rw [squarefreePrimeRootDensity,
    quadraticCongruenceRootCountTotal_primeFamily_prod]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  rw [primeQuadraticRootDensity,
    quadraticCongruenceRootCountTotal_crtCoordinate]

/-- Restriction of the literal global standard character to one CRT coordinate. -/
def squarefreePrimeRestrictedAddChar
    {k : ℕ} (P : SquarefreePrimeFamily k) (j : ZMod P.product) (i : Fin k) :
    AddChar (ZMod (P.primeValue i)) ℂ :=
  (ZMod.stdAddChar.mulShift (-j)).compAddMonoidHom
    ((AddEquiv.toAddMonoidHom (RingEquiv.toAddEquiv
      (GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).symm)).comp
        (AddMonoidHom.single (fun i => ZMod (P.primeValue i)) i))

/-- The literal global standard character factors into its actual coordinate restrictions. -/
theorem squarefreePrime_stdAddChar_factor
    {k : ℕ} (P : SquarefreePrimeFamily k) (j : ZMod P.product)
    (h : squarefreePrimeResidues P) :
    ZMod.stdAddChar (-(j *
      (GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).symm h)) =
      ∏ i, squarefreePrimeRestrictedAddChar P j i (h i) := by
  let E := GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P
  let ψ := ZMod.stdAddChar.mulShift (-j)
  have hfactor : ψ (E.symm h) = ∏ i, ψ (E.symm (Pi.single i (h i))) := by
    calc
      ψ (E.symm h) = ψ (E.symm (∑ i, Pi.single i (h i))) := by
        rw [Finset.univ_sum_single]
      _ = ψ (∑ i, E.symm (Pi.single i (h i))) := by
        rw [map_sum]
      _ = ∏ i, ψ (E.symm (Pi.single i (h i))) := by
        simpa using GaloisForLFunctions.HTGeometry.addChar_map_finsetSum ψ Finset.univ
          (fun i => E.symm (Pi.single i (h i)))
  simpa [ψ, E, squarefreePrimeRestrictedAddChar, AddChar.mulShift, mul_comm] using hfactor

/-- A coordinate restriction is trivial exactly when that CRT frequency coordinate vanishes. -/
theorem squarefreePrimeRestrictedAddChar_eq_one_iff
    {k : ℕ} (P : SquarefreePrimeFamily k) (j : ZMod P.product) (i : Fin k) :
    squarefreePrimeRestrictedAddChar P j i = 1 ↔
      (GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P j) i = 0 := by
  let E := GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P
  constructor
  · intro hψ
    have hval := DFunLike.congr_fun hψ (1 : ZMod (P.primeValue i))
    have hz : -(j * E.symm (Pi.single i 1)) = 0 := by
      apply ZMod.injective_stdAddChar
      simpa [squarefreePrimeRestrictedAddChar, E, AddChar.mulShift] using hval
    have hmul : j * E.symm (Pi.single i 1) = 0 := neg_eq_zero.mp hz
    have hmap := congrArg E hmul
    have hi := congrFun hmap i
    simpa [map_mul, Pi.single_apply] using hi
  · intro hj
    have hjE : E j i = 0 := by simpa [E] using hj
    ext x
    have hmul : j * E.symm (Pi.single i x) = 0 := by
      apply E.injective
      ext t
      by_cases hti : t = i
      · subst t
        simp [map_mul, hjE]
      · simp [map_mul, hti]
    simp [squarefreePrimeRestrictedAddChar, E, AddChar.mulShift, hmul]

/-- Literal left-hand side of `(SG5)` on the squarefree product modulus. -/
def squarefreePrimeRootDensityFourier
    {k : ℕ} (P : SquarefreePrimeFamily k) (j : ZMod P.product) : ℂ :=
  ∑ h : ZMod P.product,
    (quadraticCongruenceRootCountTotal P.product (h.val : ℤ) : ℕ) *
      ZMod.stdAddChar (-(j * h))

/-- Exact diagonal product on CRT frequency coordinates. -/
def squarefreePrimeShearDiagonal
    {k : ℕ} (P : SquarefreePrimeFamily k) (j : ZMod P.product) : ℂ :=
  ∏ i, primeShearFourierDiagonal (P.primeValue i)
    ((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P j) i)

/-- `(SG5)`: the Fourier transform of the actual squarefree quadratic-root density is exactly the
diagonal of the Boolean shear tensor. -/
theorem squarefreePrimeRootDensity_fourier
    {k : ℕ} (P : SquarefreePrimeFamily k) (j : ZMod P.product) :
    squarefreePrimeRootDensityFourier P j = squarefreePrimeShearDiagonal P j := by
  classical
  letI (i : Fin k) : NeZero (P.primeValue i) := ⟨(P.prime i).ne_zero⟩
  let E := GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P
  let f : ZMod P.product → ℂ := fun h =>
    (quadraticCongruenceRootCountTotal P.product (h.val : ℤ) : ℕ) *
      ZMod.stdAddChar (-(j * h))
  rw [squarefreePrimeRootDensityFourier]
  change (∑ h, f h) = _
  rw [show (∑ h, f h) = ∑ h : squarefreePrimeResidues P, f (E.symm h) by
    simpa using E.toEquiv.sum_comp (fun h : squarefreePrimeResidues P => f (E.symm h))]
  change (∑ h : squarefreePrimeResidues P,
      squarefreePrimeRootDensity P h * ZMod.stdAddChar (-(j * E.symm h))) = _
  dsimp only [E]
  simp_rw [squarefreePrimeRootDensity_eq_prod]
  simp_rw [squarefreePrime_stdAddChar_factor]
  simp_rw [← Finset.prod_mul_distrib]
  rw [show (∑ x : squarefreePrimeResidues P,
      ∏ i, primeQuadraticRootDensity (P.primeValue i) (x i) *
        squarefreePrimeRestrictedAddChar P j i (x i)) =
      ∏ i, ∑ h : ZMod (P.primeValue i),
        primeQuadraticRootDensity (P.primeValue i) h *
          squarefreePrimeRestrictedAddChar P j i h by
    exact (Fintype.prod_sum fun i h =>
      primeQuadraticRootDensity (P.primeValue i) h *
        squarefreePrimeRestrictedAddChar P j i h).symm]
  rw [squarefreePrimeShearDiagonal]
  apply Finset.prod_congr rfl
  intro i _
  have hlocal := primeQuadraticRootDensity_addChar_fourier (P.prime i)
    (squarefreePrimeRestrictedAddChar P j i)
  rw [if_congr (squarefreePrimeRestrictedAddChar_eq_one_iff P j i) rfl rfl] at hlocal
  simpa [primeQuadraticRootDensityAddCharFourier, primeShearFourierDiagonal] using hlocal

/-- Local Boolean shear kernel on the actual prime residue ring. -/
def primeShearKernel (p : ℕ) : Matrix (ZMod p) (ZMod p) ℂ :=
  localShearKernel (p : ℂ) (0 : ZMod p)

/-- Bi-Fourier transform of one prime shear kernel against arbitrary additive characters. -/
def primeShearKernelAddCharBiFourier
    (p : ℕ) (hp : p.Prime) (ψ φ : AddChar (ZMod p) ℂ) : ℂ := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact ∑ a : ZMod p, ∑ b : ZMod p, primeShearKernel p a b * ψ a * φ b

/-- Exact arbitrary-character bi-Fourier transform of the local shear kernel. -/
theorem primeShearKernel_addChar_biFourier
    {p : ℕ} (hp : p.Prime) (ψ φ : AddChar (ZMod p) ℂ) :
    primeShearKernelAddCharBiFourier p hp ψ φ =
      p ^ (2 : ℕ) * (if ψ = 1 ∨ φ = 1 then 1 else 0) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hψsum : (∑ a : ZMod p, ψ a) = if ψ = 1 then p else 0 := by
    by_cases hψ : ψ = 1
    · subst ψ
      simp
    · rw [AddChar.sum_eq_zero_of_ne_one hψ]
      simp [hψ]
  have hφsum : (∑ b : ZMod p, φ b) = if φ = 1 then p else 0 := by
    by_cases hφ : φ = 1
    · subst φ
      simp
    · rw [AddChar.sum_eq_zero_of_ne_one hφ]
      simp [hφ]
  rw [primeShearKernelAddCharBiFourier]
  change (∑ a : ZMod p, ∑ b : ZMod p,
    ((p : ℂ) * (if a = 0 then 1 else 0) +
      p * (if b = 0 then 1 else 0) - 1) * ψ a * φ b) = _
  calc
    _ = (p : ℂ) * (∑ b : ZMod p, φ b) +
        (p : ℂ) * (∑ a : ZMod p, ψ a) -
          (∑ a : ZMod p, ψ a) * (∑ b : ZMod p, φ b) := by
      simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      rw [hψsum, hφsum]
      by_cases hψ : ψ = 1 <;> by_cases hφ : φ = 1 <;> simp [hψ, hφ]
      all_goals ring

/-- Tensor product of local prime shear kernels in canonical CRT coordinates. -/
def squarefreePrimeShearKernel
    {k : ℕ} (P : SquarefreePrimeFamily k) (j q : ZMod P.product) : ℂ :=
  ∏ i, primeShearKernel (P.primeValue i)
    ((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P j) i)
    ((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P q) i)

/-- The tensor shear kernel has the root-density Fourier multiplier on its diagonal. -/
theorem squarefreePrimeShearKernel_diagonal
    {k : ℕ} (P : SquarefreePrimeFamily k) (j : ZMod P.product) :
    squarefreePrimeShearKernel P j j = squarefreePrimeShearDiagonal P j := by
  rw [squarefreePrimeShearKernel, squarefreePrimeShearDiagonal]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi :
      (GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P j) i = 0
  · simp [primeShearKernel, primeShearFourierDiagonal, localShearKernel, hi]
    ring
  · simp [primeShearKernel, primeShearFourierDiagonal, localShearKernel, hi]

/-- Literal bi-Fourier transform of the squarefree tensor shear kernel. -/
def squarefreePrimeShearKernelBiFourier
    {k : ℕ} (P : SquarefreePrimeFamily k) (x y : ZMod P.product) : ℂ :=
  ∑ j : ZMod P.product, ∑ q : ZMod P.product,
    squarefreePrimeShearKernel P j q * ZMod.stdAddChar (-(j * x)) *
      ZMod.stdAddChar (q * y)

/-- `(SG6)`, scalar form: the tensor shear kernel transforms to the zero-product incidence
kernel, with exact unnormalized scale `l²`. -/
theorem squarefreePrimeShearKernel_biFourier
    {k : ℕ} (P : SquarefreePrimeFamily k) (x y : ZMod P.product) :
    squarefreePrimeShearKernelBiFourier P x y =
      (P.product : ℂ) ^ (2 : ℕ) * (if x * y = 0 then 1 else 0) := by
  classical
  letI (i : Fin k) : NeZero (P.primeValue i) := ⟨(P.prime i).ne_zero⟩
  let E := GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P
  let g : ZMod P.product → ZMod P.product → ℂ := fun j q =>
    squarefreePrimeShearKernel P j q * ZMod.stdAddChar (-(j * x)) *
      ZMod.stdAddChar (q * y)
  rw [squarefreePrimeShearKernelBiFourier]
  change (∑ j, ∑ q, g j q) = _
  rw [show (∑ j, ∑ q, g j q) =
      ∑ a : squarefreePrimeResidues P, ∑ b : squarefreePrimeResidues P,
        g (E.symm a) (E.symm b) by
    calc
      (∑ j, ∑ q, g j q) =
          ∑ j, ∑ b : squarefreePrimeResidues P, g j (E.symm b) := by
        apply Finset.sum_congr rfl
        intro j _
        simpa using E.toEquiv.sum_comp
          (fun b : squarefreePrimeResidues P => g j (E.symm b))
      _ = _ := by
        simpa using E.toEquiv.sum_comp
          (fun a : squarefreePrimeResidues P =>
            ∑ b : squarefreePrimeResidues P, g (E.symm a) (E.symm b))]
  have hxchar (a : squarefreePrimeResidues P) :
      ZMod.stdAddChar (-(E.symm a * x)) =
        ∏ i, squarefreePrimeRestrictedAddChar P x i (a i) := by
    simpa [mul_comm] using squarefreePrime_stdAddChar_factor P x a
  have hychar (b : squarefreePrimeResidues P) :
      ZMod.stdAddChar (E.symm b * y) =
        ∏ i, squarefreePrimeRestrictedAddChar P (-y) i (b i) := by
    simpa [mul_comm] using squarefreePrime_stdAddChar_factor P (-y) b
  change (∑ a : squarefreePrimeResidues P, ∑ b : squarefreePrimeResidues P,
      squarefreePrimeShearKernel P (E.symm a) (E.symm b) *
        ZMod.stdAddChar (-(E.symm a * x)) * ZMod.stdAddChar (E.symm b * y)) = _
  dsimp only [E]
  simp_rw [squarefreePrimeShearKernel]
  simp_rw [RingEquiv.apply_symm_apply]
  rw [show (∑ a : squarefreePrimeResidues P, ∑ b : squarefreePrimeResidues P,
      (∏ i, primeShearKernel (P.primeValue i) (a i) (b i)) *
        ZMod.stdAddChar (-((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).symm a * x)) *
          ZMod.stdAddChar
            ((GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P).symm b * y)) =
      ∑ a : squarefreePrimeResidues P, ∑ b : squarefreePrimeResidues P,
        ∏ i, (primeShearKernel (P.primeValue i) (a i) (b i) *
          squarefreePrimeRestrictedAddChar P x i (a i)) *
            squarefreePrimeRestrictedAddChar P (-y) i (b i) by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hxchar a, hychar b, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]]
  rw [show (∑ a : squarefreePrimeResidues P, ∑ b : squarefreePrimeResidues P,
      ∏ i, (primeShearKernel (P.primeValue i) (a i) (b i) *
        squarefreePrimeRestrictedAddChar P x i (a i)) *
          squarefreePrimeRestrictedAddChar P (-y) i (b i)) =
      ∏ i, ∑ a : ZMod (P.primeValue i), ∑ b : ZMod (P.primeValue i),
        (primeShearKernel (P.primeValue i) a b *
          squarefreePrimeRestrictedAddChar P x i a) *
            squarefreePrimeRestrictedAddChar P (-y) i b by
    rw [Finset.sum_comm]
    calc
      (∑ b : squarefreePrimeResidues P, ∑ a : squarefreePrimeResidues P,
          ∏ i, (primeShearKernel (P.primeValue i) (a i) (b i) *
            squarefreePrimeRestrictedAddChar P x i (a i)) *
              squarefreePrimeRestrictedAddChar P (-y) i (b i)) =
          ∑ b : squarefreePrimeResidues P,
            ∏ i, ∑ a : ZMod (P.primeValue i),
              (primeShearKernel (P.primeValue i) a (b i) *
                squarefreePrimeRestrictedAddChar P x i a) *
                  squarefreePrimeRestrictedAddChar P (-y) i (b i) := by
        apply Finset.sum_congr rfl
        intro b _
        exact (Fintype.prod_sum fun i a =>
          (primeShearKernel (P.primeValue i) a (b i) *
            squarefreePrimeRestrictedAddChar P x i a) *
              squarefreePrimeRestrictedAddChar P (-y) i (b i)).symm
      _ = _ := by
        rw [show (∑ b : squarefreePrimeResidues P,
            ∏ i, ∑ a : ZMod (P.primeValue i),
              (primeShearKernel (P.primeValue i) a (b i) *
                squarefreePrimeRestrictedAddChar P x i a) *
                  squarefreePrimeRestrictedAddChar P (-y) i (b i)) =
            ∏ i, ∑ b : ZMod (P.primeValue i),
              ∑ a : ZMod (P.primeValue i),
                (primeShearKernel (P.primeValue i) a b *
                  squarefreePrimeRestrictedAddChar P x i a) *
                    squarefreePrimeRestrictedAddChar P (-y) i b by
          exact (Fintype.prod_sum fun i b =>
            ∑ a : ZMod (P.primeValue i),
              (primeShearKernel (P.primeValue i) a b *
                squarefreePrimeRestrictedAddChar P x i a) *
                  squarefreePrimeRestrictedAddChar P (-y) i b).symm]
        apply Finset.prod_congr rfl
        intro i _
        rw [Finset.sum_comm]]
  have hlocal (i : Fin k) := primeShearKernel_addChar_biFourier (P.prime i)
    (squarefreePrimeRestrictedAddChar P x i)
    (squarefreePrimeRestrictedAddChar P (-y) i)
  rw [show (∏ i, ∑ a : ZMod (P.primeValue i), ∑ b : ZMod (P.primeValue i),
      (primeShearKernel (P.primeValue i) a b *
        squarefreePrimeRestrictedAddChar P x i a) *
          squarefreePrimeRestrictedAddChar P (-y) i b) =
      ∏ i, (P.primeValue i : ℂ) ^ (2 : ℕ) *
        (if squarefreePrimeRestrictedAddChar P x i = 1 ∨
            squarefreePrimeRestrictedAddChar P (-y) i = 1 then 1 else 0) by
    apply Finset.prod_congr rfl
    intro i _
    simpa [primeShearKernelAddCharBiFourier] using hlocal i]
  have htrivial (i : Fin k) :
      squarefreePrimeRestrictedAddChar P x i = 1 ∨
          squarefreePrimeRestrictedAddChar P (-y) i = 1 ↔
        (E x i) * (E y i) = 0 := by
    rw [squarefreePrimeRestrictedAddChar_eq_one_iff,
      squarefreePrimeRestrictedAddChar_eq_one_iff]
    simp only [map_neg, Pi.neg_apply, neg_eq_zero]
    letI : Fact (P.primeValue i).Prime := ⟨P.prime i⟩
    exact (mul_eq_zero).symm
  simp_rw [if_congr (htrivial _) rfl rfl]
  rw [Finset.prod_mul_distrib]
  have hscale : (∏ i, ((P.primeValue i : ℕ) : ℂ) ^ (2 : ℕ)) = (P.product : ℂ) ^ (2 : ℕ) := by
    rw [Finset.prod_pow]
    rw [GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.product]
    push_cast
    congr 1
  rw [hscale]
  congr 1
  by_cases hxy : x * y = 0
  · rw [if_pos hxy]
    apply Finset.prod_eq_one
    intro i _
    have hi := congrFun (congrArg E hxy) i
    simp only [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply] at hi
    simp [hi]
  · rw [if_neg hxy]
    have hnotall : ¬ ∀ i, E x i * E y i = 0 := by
      intro hall
      apply hxy
      apply E.injective
      ext i
      simpa [map_mul] using hall i
    push Not at hnotall
    obtain ⟨i, hi⟩ := hnotall
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

/-- Unnormalized Fourier packet of Hilbert-space coefficients. -/
def squarefreePrimeFourierPacket
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) (j : ZMod P.product) : H :=
  ∑ x, ZMod.stdAddChar (j * x) • ξ x

/-- Shear quadratic form evaluated on unnormalized Fourier packets. -/
def squarefreePrimeShearPacketForm
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) : ℂ :=
  ∑ j, ∑ q, squarefreePrimeShearKernel P j q *
    inner ℂ (squarefreePrimeFourierPacket P ξ j) (squarefreePrimeFourierPacket P ξ q)

/-- Zero-product incidence Gram form of the coefficient family. -/
def squarefreePrimeZeroProductGram
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) : ℂ :=
  ∑ x, ∑ y, if x * y = 0 then inner ℂ (ξ x) (ξ y) else 0

/- `(SG6)`, Hilbert form: shear quadratic form equals `l²` times the exact zero-product Gram
form of the original coefficients. -/
set_option maxHeartbeats 800000 in
theorem squarefreePrimeShearPacketForm_eq_zeroProductGram
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) :
    squarefreePrimeShearPacketForm P ξ =
      (P.product : ℂ) ^ (2 : ℕ) * squarefreePrimeZeroProductGram P ξ := by
  classical
  let T : ZMod P.product → ZMod P.product → ZMod P.product →
      ZMod P.product → ℂ := fun j q y x =>
    squarefreePrimeShearKernel P j q *
      (ZMod.stdAddChar (q * y) *
        (ZMod.stdAddChar (-(j * x)) * inner ℂ (ξ x) (ξ y)))
  rw [squarefreePrimeShearPacketForm]
  have hstar (z : ZMod P.product) :
      star (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    rw [RCLike.star_def]
    exact (AddChar.map_neg_eq_conj ZMod.stdAddChar z).symm
  simp only [squarefreePrimeFourierPacket, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, starRingEnd_apply]
  simp_rw [hstar]
  simp only [Finset.mul_sum]
  change (∑ j, ∑ q, ∑ y, ∑ x, T j q y x) = _
  calc
    _ = ∑ j, ∑ q, ∑ x, ∑ y, T j q y x := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro q _
      exact Finset.sum_comm
    _ = ∑ j, ∑ x, ∑ q, ∑ y, T j q y x := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ x, ∑ j, ∑ q, ∑ y, T j q y x := Finset.sum_comm
    _ = ∑ x, ∑ j, ∑ y, ∑ q, T j q y x := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ j, ∑ q, T j q y x := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ x, ∑ y,
        squarefreePrimeShearKernelBiFourier P x y * inner ℂ (ξ x) (ξ y) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ j, ∑ q, T j q y x) =
            ∑ j, ∑ q,
              (squarefreePrimeShearKernel P j q * ZMod.stdAddChar (-(j * x)) *
                ZMod.stdAddChar (q * y)) * inner ℂ (ξ x) (ξ y) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro q _
          simp [T]
          ring
        _ = (∑ j, ∑ q,
              squarefreePrimeShearKernel P j q * ZMod.stdAddChar (-(j * x)) *
                ZMod.stdAddChar (q * y)) * inner ℂ (ξ x) (ξ y) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
        _ = _ := rfl
    _ = ∑ x, ∑ y,
        ((P.product : ℂ) ^ (2 : ℕ) * (if x * y = 0 then 1 else 0)) *
          inner ℂ (ξ x) (ξ y) := by
      simp_rw [squarefreePrimeShearKernel_biFourier]
    _ = (P.product : ℂ) ^ (2 : ℕ) * squarefreePrimeZeroProductGram P ξ := by
      rw [squarefreePrimeZeroProductGram, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hxy : x * y = 0 <;> simp [hxy]

end

end RHTower
