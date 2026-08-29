import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinRamanujanDirichletSeries
import GaloisForLFunctions.RHTower.Sieve.PerronFiniteSum

/-!
# Exact primitive-cusp reindexing of the Eisenstein Poincare series

Corpus search isolated the missing geometric weld between the absolutely convergent primitive-pair
Poincare series and the fixed-positive-denominator Ramanujan slices.  For every positive modulus,
this module constructs the exact equivalence

`(unit residue modulo Q, integer translate) equiv (integer coprime to Q)`

and proves that the scaled periodized Cauchy kernel is literally the corresponding Poincare seed.
Absolute summability is inherited through injective restriction from the corpus primitive-series
convergence theorem, so every product, sigma, and sign reindexing is unconditional.

The headline identity is

`E_raw(z,s) = y^s + sum_(Q>0) positivePrimitiveCuspSlice(z,s,Q,x)`.

It accounts for both signs of each primitive pair, the two first-row terms, and the conventional
factor `1/2`.  This closes the geometric side of the actual Poincare/Fourier coefficient
assembly.  Combined with the corpus fixed-slice Fourier theorem, exact Cauchy Fourier--Bessel
transform, and Ramanujan Dirichlet series, it feeds the route-killing chain

`exact Poincare coefficient -> Fourier uniqueness -> modular Green/Stokes defects ->
balanced polarized BM coefficient -> negative BM leg -> conserved left-QNM projection ->
HC94 clock defect -> RH`.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HB] [FZZ-P] [RBH] [PW-B]`
-/

open Complex Real Finset Filter Topology MeasureTheory Set
open scoped BigOperators NNReal FourierTransform

namespace RHTower
noncomputable section

theorem d4BM_isUnit_intCast_iff_gcd_eq_one
    (Q : CGLPositiveModulus) (d : ℤ) :
    IsUnit (d : ZMod Q.value) ↔ Int.gcd (Q.value : ℤ) d = 1 := by
  rw [Int.gcd_eq_natAbs]
  cases d with
  | ofNat n =>
      simpa [Nat.coprime_comm] using
        (ZMod.isUnit_iff_coprime n Q.value)
  | negSucc n =>
      rw [show ((Int.negSucc n : ℤ) : ZMod Q.value) = -((n + 1 : ℕ) : ZMod Q.value) by
        push_cast
        rfl]
      have hneg : IsUnit (-((n + 1 : ℕ) : ZMod Q.value)) ↔
          IsUnit ((n + 1 : ℕ) : ZMod Q.value) := by
        constructor <;> intro h
        · simpa using h.neg
        · exact h.neg
      rw [hneg]
      simpa [Nat.coprime_comm] using
        (ZMod.isUnit_iff_coprime (n + 1) Q.value)

abbrev D4BMUnitResidueTranslateIndex (Q : CGLPositiveModulus) :=
  {a : ZMod Q.value // IsUnit a} × ℤ

abbrev D4BMCoprimeInteger (Q : CGLPositiveModulus) :=
  {d : ℤ // Int.gcd (Q.value : ℤ) d = 1}

def d4BMUnitResidueTranslateToCoprimeInteger
    (Q : CGLPositiveModulus) (p : D4BMUnitResidueTranslateIndex Q) :
    D4BMCoprimeInteger Q := by
  letI : NeZero Q.value := ⟨Q.positive.ne'⟩
  let d : ℤ := (p.1.1.val : ℤ) + (Q.value : ℤ) * p.2
  refine ⟨d, (d4BM_isUnit_intCast_iff_gcd_eq_one Q d).mp ?_⟩
  have hd : (d : ZMod Q.value) = p.1.1 := by
    dsimp [d]
    push_cast
    simp
  rw [hd]
  exact p.1.2

def d4BMCoprimeIntegerToUnitResidueTranslate
    (Q : CGLPositiveModulus) (d : D4BMCoprimeInteger Q) :
    D4BMUnitResidueTranslateIndex Q :=
  (⟨(d.1 : ZMod Q.value),
      (d4BM_isUnit_intCast_iff_gcd_eq_one Q d.1).mpr d.2⟩,
    d.1 / (Q.value : ℤ))

theorem d4BMUnitResidueTranslate_leftInverse (Q : CGLPositiveModulus) :
    Function.LeftInverse (d4BMCoprimeIntegerToUnitResidueTranslate Q)
      (d4BMUnitResidueTranslateToCoprimeInteger Q) := by
  intro p
  letI : NeZero Q.value := ⟨Q.positive.ne'⟩
  apply Prod.ext
  · apply Subtype.ext
    change (((((p.1.1.val : ℤ) + (Q.value : ℤ) * p.2) : ℤ) :
      ZMod Q.value)) = p.1.1
    push_cast
    simp
  · change ((p.1.1.val : ℤ) + (Q.value : ℤ) * p.2) / (Q.value : ℤ) = p.2
    have hQ : (0 : ℤ) < (Q.value : ℤ) := by exact_mod_cast Q.positive
    exact ((Int.ediv_emod_unique (a := (p.1.1.val : ℤ) + (Q.value : ℤ) * p.2)
      (b := (Q.value : ℤ)) (r := (p.1.1.val : ℤ)) (q := p.2) hQ).mpr
        ⟨by ring, by positivity, by exact_mod_cast p.1.1.val_lt⟩).1

theorem d4BMUnitResidueTranslate_rightInverse (Q : CGLPositiveModulus) :
    Function.RightInverse (d4BMCoprimeIntegerToUnitResidueTranslate Q)
      (d4BMUnitResidueTranslateToCoprimeInteger Q) := by
  intro d
  letI : NeZero Q.value := ⟨Q.positive.ne'⟩
  apply Subtype.ext
  change ((((d.1 : ZMod Q.value).val : ℕ) : ℤ) +
      (Q.value : ℤ) * (d.1 / (Q.value : ℤ))) = d.1
  rw [ZMod.val_intCast]
  have h := Int.ediv_mul_add_emod d.1 (Q.value : ℤ)
  linarith

def d4BMUnitResidueTranslateEquivCoprimeInteger (Q : CGLPositiveModulus) :
    D4BMUnitResidueTranslateIndex Q ≃ D4BMCoprimeInteger Q where
  toFun := d4BMUnitResidueTranslateToCoprimeInteger Q
  invFun := d4BMCoprimeIntegerToUnitResidueTranslate Q
  left_inv := d4BMUnitResidueTranslate_leftInverse Q
  right_inv := d4BMUnitResidueTranslate_rightInverse Q

def d4BMCoprimeIntegerToPrimitivePair
    (Q : CGLPositiveModulus) (d : D4BMCoprimeInteger Q) :
    D4BMPrimitiveIntegerPair :=
  ⟨((Q.value : ℤ), d.1), d.2⟩

theorem d4BMCoprimeIntegerToPrimitivePair_injective (Q : CGLPositiveModulus) :
    Function.Injective (d4BMCoprimeIntegerToPrimitivePair Q) := by
  intro d e h
  apply Subtype.ext
  exact congrArg (fun p : D4BMPrimitiveIntegerPair => p.pair.2) h

def d4BMUnitResidueTranslateToPrimitivePair
    (Q : CGLPositiveModulus) (p : D4BMUnitResidueTranslateIndex Q) :
    D4BMPrimitiveIntegerPair :=
  d4BMCoprimeIntegerToPrimitivePair Q
    (d4BMUnitResidueTranslateEquivCoprimeInteger Q p)

theorem d4BMUnitResidueTranslateToPrimitivePair_injective
    (Q : CGLPositiveModulus) :
    Function.Injective (d4BMUnitResidueTranslateToPrimitivePair Q) :=
  (d4BMCoprimeIntegerToPrimitivePair_injective Q).comp
    (d4BMUnitResidueTranslateEquivCoprimeInteger Q).injective

theorem d4BM_poincareSeed_fixedPositiveDenominator
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) (d : D4BMCoprimeInteger Q) :
    d4BMPoincareSeed z P.s (d4BMCoprimeIntegerToPrimitivePair Q d) =
      (z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s)) *
        d4BMCauchyPowerKernel z P.s (z.x + (d.1 : ℝ) / Q.value) := by
  have hQ : (0 : ℝ) < Q.value := by exact_mod_cast Q.positive
  let K : ℝ := z.y ^ 2 + (z.x + (d.1 : ℝ) / Q.value) ^ 2
  have hK : 0 < K := by
    dsimp [K]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos z.y_pos) (sq_nonneg _)
  have hquad :
      d4BMPoincareQuadratic z ((Q.value : ℤ), d.1) =
        (Q.value : ℝ) ^ 2 * K := by
    dsimp [d4BMPoincareQuadratic, K]
    push_cast
    field_simp
  rw [d4BMPoincareSeed, d4BMCoprimeIntegerToPrimitivePair, hquad]
  rw [RHTower.Sieve.ofReal_div_cpow_eq_mul_cpow_neg z.y_pos
    (mul_pos (sq_pos_of_pos hQ) hK) P.s]
  unfold d4BMCauchyPowerKernel
  change (z.y : ℂ) ^ P.s *
      ((((Q.value : ℝ) ^ 2 * K : ℝ) : ℂ)) ^ (-P.s) =
    (z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s)) *
      ((K : ℝ) : ℂ) ^ (-P.s)
  rw [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg (sq_nonneg _) hK.le]
  rw [pow_two, Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hQ.le hQ.le]
  have hQne : ((Q.value : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Q.positive.ne'
  have hpow : ((Q.value : ℝ) : ℂ) ^ (-P.s) *
      ((Q.value : ℝ) : ℂ) ^ (-P.s) =
      ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s)) := by
    rw [← Complex.cpow_add _ _ hQne]
    congr 1
    ring
  rw [hpow]
  ring

theorem d4BM_summable_scaledUnitResidueTranslateKernel
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) :
    Summable (fun p : D4BMUnitResidueTranslateIndex Q =>
      (z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s)) *
        d4BMCauchyPowerKernel z P.s
          (z.x + (p.1.1.val : ℝ) / Q.value + p.2)) := by
  have hseed := (summable_d4BMPoincareSeed z P).comp_injective
    (d4BMUnitResidueTranslateToPrimitivePair_injective Q)
  apply hseed.congr
  intro p
  change d4BMPoincareSeed z P.s
      (d4BMCoprimeIntegerToPrimitivePair Q
        (d4BMUnitResidueTranslateEquivCoprimeInteger Q p)) = _
  rw [d4BM_poincareSeed_fixedPositiveDenominator]
  have harg : z.x +
      (((d4BMUnitResidueTranslateEquivCoprimeInteger Q p).1 : ℤ) : ℝ) / Q.value =
      z.x + (p.1.1.val : ℝ) / Q.value + p.2 := by
    change z.x +
        (((p.1.1.val : ℤ) + (Q.value : ℤ) * p.2 : ℤ) : ℝ) / Q.value =
      z.x + (p.1.1.val : ℝ) / Q.value + p.2
    push_cast
    have hQne : (Q.value : ℝ) ≠ 0 := by exact_mod_cast Q.positive.ne'
    field_simp [hQne]
    ring
  rw [harg]

theorem d4BM_positivePrimitiveCuspSlice_eq_tsum_coprimeInteger
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter)
    (Q : CGLPositiveModulus) :
    d4BMPositivePrimitiveCuspSlice z P Q z.x =
      ∑' d : D4BMCoprimeInteger Q,
        d4BMPoincareSeed z P.s (d4BMCoprimeIntegerToPrimitivePair Q d) := by
  let C : ℂ := (z.y : ℂ) ^ P.s * ((Q.value : ℝ) : ℂ) ^ (-(2 * P.s))
  let F : D4BMUnitResidueTranslateIndex Q → ℂ := fun p =>
    C * d4BMCauchyPowerKernel z P.s
      (z.x + (p.1.1.val : ℝ) / Q.value + p.2)
  have hF : Summable F := by
    simpa [F, C] using d4BM_summable_scaledUnitResidueTranslateKernel z P Q
  letI : Fintype {a : ZMod Q.value // IsUnit a} := Fintype.ofFinite _
  rw [← (d4BMUnitResidueTranslateEquivCoprimeInteger Q).tsum_eq
    (fun d : D4BMCoprimeInteger Q =>
      d4BMPoincareSeed z P.s (d4BMCoprimeIntegerToPrimitivePair Q d))]
  have hterm : ∀ p : D4BMUnitResidueTranslateIndex Q,
      d4BMPoincareSeed z P.s
          (d4BMCoprimeIntegerToPrimitivePair Q
            (d4BMUnitResidueTranslateEquivCoprimeInteger Q p)) = F p := by
    intro p
    rw [d4BM_poincareSeed_fixedPositiveDenominator]
    dsimp [F, C]
    have harg : z.x +
        (((d4BMUnitResidueTranslateEquivCoprimeInteger Q p).1 : ℤ) : ℝ) / Q.value =
        z.x + (p.1.1.val : ℝ) / Q.value + p.2 := by
      change z.x +
          (((p.1.1.val : ℤ) + (Q.value : ℤ) * p.2 : ℤ) : ℝ) / Q.value =
        z.x + (p.1.1.val : ℝ) / Q.value + p.2
      push_cast
      have hQne : (Q.value : ℝ) ≠ 0 := by exact_mod_cast Q.positive.ne'
      field_simp [hQne]
      ring
    rw [harg]
  rw [tsum_congr hterm]
  change C *
      (∑ a ∈ (Finset.univ : Finset (ZMod Q.value)).filter IsUnit,
        ∑' k : ℤ,
          d4BMCauchyPowerKernel z P.s
            (z.x + (a.val : ℝ) / Q.value + k)) = ∑' p, F p
  rw [Finset.mul_sum]
  simp_rw [← tsum_mul_left]
  rw [Finset.sum_subtype (p := fun a : ZMod Q.value => IsUnit a)
    ((Finset.univ : Finset (ZMod Q.value)).filter IsUnit)
    (by intro a; simp) (fun a : ZMod Q.value =>
      ∑' k : ℤ, C * d4BMCauchyPowerKernel z P.s
        (z.x + (a.val : ℝ) / Q.value + k))]
  rw [hF.tsum_prod]
  rw [tsum_eq_sum (s := Finset.univ) (by simp)]

def d4BMPositiveModulusOfPNat (Q : ℕ+) : CGLPositiveModulus :=
  ⟨Q.1, Q.2⟩

abbrev D4BMPositiveCuspIndex :=
  (Q : ℕ+) × D4BMCoprimeInteger (d4BMPositiveModulusOfPNat Q)

abbrev D4BMPositivePrimitivePair :=
  {p : D4BMPrimitiveIntegerPair // 0 < p.pair.1}

theorem d4BMPrimitiveIntegerPair_ext
    {p q : D4BMPrimitiveIntegerPair} (h : p.pair = q.pair) : p = q := by
  cases p
  cases q
  simp_all

def d4BMPositiveCuspIndexToPrimitivePair
    (I : D4BMPositiveCuspIndex) : D4BMPositivePrimitivePair :=
  ⟨d4BMCoprimeIntegerToPrimitivePair (d4BMPositiveModulusOfPNat I.1) I.2,
    by change 0 < (I.1.1 : ℤ); exact_mod_cast I.1.2⟩

theorem d4BMPositiveCuspIndexToPrimitivePair_injective :
    Function.Injective d4BMPositiveCuspIndexToPrimitivePair := by
  rintro ⟨Q, d⟩ ⟨R, e⟩ h
  have hpair := congrArg
    (fun p : D4BMPositivePrimitivePair => p.1.pair) h
  change ((Q.1 : ℤ), d.1) = ((R.1 : ℤ), e.1) at hpair
  have hQz : (Q.1 : ℤ) = (R.1 : ℤ) := by
    simpa using congrArg Prod.fst hpair
  have hQnat : Q.1 = R.1 := by
    exact_mod_cast hQz
  have hQR : Q = R := PNat.eq hQnat
  subst R
  have hde : d = e := Subtype.ext (congrArg Prod.snd hpair)
  subst e
  rfl

theorem d4BMPositiveCuspIndexToPrimitivePair_surjective :
    Function.Surjective d4BMPositiveCuspIndexToPrimitivePair := by
  intro p
  have hc0 : ((p.1.pair.1.toNat : ℕ) : ℤ) = p.1.pair.1 :=
    Int.toNat_of_nonneg p.2.le
  have hcpos : 0 < p.1.pair.1.toNat := by omega
  let Q : ℕ+ := ⟨p.1.pair.1.toNat, hcpos⟩
  let M : CGLPositiveModulus := d4BMPositiveModulusOfPNat Q
  have hc : ((Q.1 : ℕ) : ℤ) = p.1.pair.1 :=
    Int.toNat_of_nonneg p.2.le
  let d : D4BMCoprimeInteger M := ⟨p.1.pair.2, by
    change Int.gcd ((Q.1 : ℕ) : ℤ) p.1.pair.2 = 1
    rw [hc]
    exact p.1.primitive⟩
  refine ⟨⟨Q, d⟩, ?_⟩
  apply Subtype.ext
  apply d4BMPrimitiveIntegerPair_ext
  apply Prod.ext
  · exact hc
  · rfl

def d4BMPositiveCuspIndexEquivPrimitivePair :
    D4BMPositiveCuspIndex ≃ D4BMPositivePrimitivePair :=
  Equiv.ofBijective d4BMPositiveCuspIndexToPrimitivePair
    ⟨d4BMPositiveCuspIndexToPrimitivePair_injective,
      d4BMPositiveCuspIndexToPrimitivePair_surjective⟩

theorem d4BM_tsum_positivePrimitiveCuspSlice_eq_positivePrimitivePairs
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∑' Q : ℕ+,
        d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) z.x) =
      ∑' p : D4BMPositivePrimitivePair, d4BMPoincareSeed z P.s p.1 := by
  have hinj : Function.Injective
      (fun I : D4BMPositiveCuspIndex =>
        (d4BMPositiveCuspIndexToPrimitivePair I).1) := by
    intro I J h
    apply d4BMPositiveCuspIndexToPrimitivePair_injective
    exact Subtype.ext h
  have hsum : Summable (fun I : D4BMPositiveCuspIndex =>
      d4BMPoincareSeed z P.s (d4BMPositiveCuspIndexToPrimitivePair I).1) :=
    (summable_d4BMPoincareSeed z P).comp_injective hinj
  rw [← d4BMPositiveCuspIndexEquivPrimitivePair.tsum_eq
    (fun p : D4BMPositivePrimitivePair => d4BMPoincareSeed z P.s p.1)]
  change (∑' Q : ℕ+,
      d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) z.x) =
    ∑' I : D4BMPositiveCuspIndex,
      d4BMPoincareSeed z P.s (d4BMPositiveCuspIndexToPrimitivePair I).1
  rw [hsum.tsum_sigma]
  apply tsum_congr
  intro Q
  exact d4BM_positivePrimitiveCuspSlice_eq_tsum_coprimeInteger z P
    (d4BMPositiveModulusOfPNat Q)

abbrev D4BMNegativePrimitivePair :=
  {p : D4BMPrimitiveIntegerPair // p.pair.1 < 0}

def d4BMNegPrimitiveIntegerPair (p : D4BMPrimitiveIntegerPair) :
    D4BMPrimitiveIntegerPair :=
  ⟨(-p.pair.1, -p.pair.2), by
    rw [Int.gcd_eq_natAbs, Int.natAbs_neg, Int.natAbs_neg,
      ← Int.gcd_eq_natAbs]
    exact p.primitive⟩

theorem d4BMNegPrimitiveIntegerPair_involutive :
    Function.Involutive d4BMNegPrimitiveIntegerPair := by
  intro p
  apply d4BMPrimitiveIntegerPair_ext
  simp [d4BMNegPrimitiveIntegerPair]

def d4BMPositivePrimitivePairEquivNegative :
    D4BMPositivePrimitivePair ≃ D4BMNegativePrimitivePair where
  toFun p := ⟨d4BMNegPrimitiveIntegerPair p.1, by
    change -p.1.pair.1 < 0
    omega⟩
  invFun p := ⟨d4BMNegPrimitiveIntegerPair p.1, by
    change 0 < -p.1.pair.1
    omega⟩
  left_inv p := by
    apply Subtype.ext
    exact d4BMNegPrimitiveIntegerPair_involutive p.1
  right_inv p := by
    apply Subtype.ext
    exact d4BMNegPrimitiveIntegerPair_involutive p.1

theorem d4BM_poincareSeed_negPrimitive
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ)
    (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed z s (d4BMNegPrimitiveIntegerPair p) =
      d4BMPoincareSeed z s p := by
  unfold d4BMPoincareSeed
  congr 2
  unfold d4BMNegPrimitiveIntegerPair d4BMPoincareQuadratic
  simp only [Int.cast_neg]
  ring

theorem d4BM_tsum_negativePrimitivePair_eq_positive
    (z : D4BMUpperHalfPlaneCoordinate) (s : ℂ) :
    (∑' p : D4BMNegativePrimitivePair, d4BMPoincareSeed z s p.1) =
      ∑' p : D4BMPositivePrimitivePair, d4BMPoincareSeed z s p.1 := by
  rw [← d4BMPositivePrimitivePairEquivNegative.tsum_eq
    (fun p : D4BMNegativePrimitivePair => d4BMPoincareSeed z s p.1)]
  apply tsum_congr
  intro p
  exact d4BM_poincareSeed_negPrimitive z s p.1

def d4BMPrimitiveSignSumToPrimitivePair :
    D4BMPrimitiveFirstRowPair ⊕
      (D4BMPositivePrimitivePair ⊕ D4BMNegativePrimitivePair) →
        D4BMPrimitiveIntegerPair
  | Sum.inl p => p.1
  | Sum.inr (Sum.inl p) => p.1
  | Sum.inr (Sum.inr p) => p.1

theorem d4BMPrimitiveSignSumToPrimitivePair_bijective :
    Function.Bijective d4BMPrimitiveSignSumToPrimitivePair := by
  constructor
  · intro a b h
    rcases a with a | a
    · rcases b with b | b
      · exact congrArg Sum.inl (Subtype.ext h)
      · rcases b with b | b
        · exfalso
          have hz : a.1.pair.1 = 0 := a.2
          have hp : 0 < b.1.pair.1 := b.2
          have heq : a.1.pair.1 = b.1.pair.1 := by
            simpa [d4BMPrimitiveSignSumToPrimitivePair] using
              congrArg (fun p : D4BMPrimitiveIntegerPair => p.pair.1) h
          omega
        · exfalso
          have hz : a.1.pair.1 = 0 := a.2
          have hn : b.1.pair.1 < 0 := b.2
          have heq : a.1.pair.1 = b.1.pair.1 := by
            simpa [d4BMPrimitiveSignSumToPrimitivePair] using
              congrArg (fun p : D4BMPrimitiveIntegerPair => p.pair.1) h
          omega
    · rcases a with a | a
      · rcases b with b | b
        · exfalso
          have hp : 0 < a.1.pair.1 := a.2
          have hz : b.1.pair.1 = 0 := b.2
          have heq : a.1.pair.1 = b.1.pair.1 := by
            simpa [d4BMPrimitiveSignSumToPrimitivePair] using
              congrArg (fun p : D4BMPrimitiveIntegerPair => p.pair.1) h
          omega
        · rcases b with b | b
          · exact congrArg (fun p => Sum.inr (Sum.inl p)) (Subtype.ext h)
          · exfalso
            have hp : 0 < a.1.pair.1 := a.2
            have hn : b.1.pair.1 < 0 := b.2
            have heq : a.1.pair.1 = b.1.pair.1 := by
              simpa [d4BMPrimitiveSignSumToPrimitivePair] using
                congrArg (fun p : D4BMPrimitiveIntegerPair => p.pair.1) h
            omega
      · rcases b with b | b
        · exfalso
          have hn : a.1.pair.1 < 0 := a.2
          have hz : b.1.pair.1 = 0 := b.2
          have heq : a.1.pair.1 = b.1.pair.1 := by
            simpa [d4BMPrimitiveSignSumToPrimitivePair] using
              congrArg (fun p : D4BMPrimitiveIntegerPair => p.pair.1) h
          omega
        · rcases b with b | b
          · exfalso
            have hn : a.1.pair.1 < 0 := a.2
            have hp : 0 < b.1.pair.1 := b.2
            have heq : a.1.pair.1 = b.1.pair.1 := by
              simpa [d4BMPrimitiveSignSumToPrimitivePair] using
                congrArg (fun p : D4BMPrimitiveIntegerPair => p.pair.1) h
            omega
          · exact congrArg (fun p => Sum.inr (Sum.inr p)) (Subtype.ext h)
  · intro p
    rcases lt_trichotomy p.pair.1 0 with hn | hz | hp
    · exact ⟨Sum.inr (Sum.inr ⟨p, hn⟩), rfl⟩
    · exact ⟨Sum.inl ⟨p, hz⟩, rfl⟩
    · exact ⟨Sum.inr (Sum.inl ⟨p, hp⟩), rfl⟩

def d4BMPrimitiveSignSumEquivPrimitivePair :
    D4BMPrimitiveFirstRowPair ⊕
      (D4BMPositivePrimitivePair ⊕ D4BMNegativePrimitivePair) ≃
        D4BMPrimitiveIntegerPair :=
  Equiv.ofBijective d4BMPrimitiveSignSumToPrimitivePair
    d4BMPrimitiveSignSumToPrimitivePair_bijective

theorem d4BM_tsum_poincareSeed_sign_decomposition
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (∑' p : D4BMPrimitiveIntegerPair, d4BMPoincareSeed z P.s p) =
      (∑' p : D4BMPrimitiveFirstRowPair, d4BMPoincareSeed z P.s p.1) +
        ((∑' p : D4BMPositivePrimitivePair, d4BMPoincareSeed z P.s p.1) +
          ∑' p : D4BMNegativePrimitivePair, d4BMPoincareSeed z P.s p.1) := by
  let f : D4BMPrimitiveFirstRowPair ⊕
      (D4BMPositivePrimitivePair ⊕ D4BMNegativePrimitivePair) → ℂ := fun p =>
    d4BMPoincareSeed z P.s (d4BMPrimitiveSignSumToPrimitivePair p)
  have hf : Summable f :=
    (summable_d4BMPoincareSeed z P).comp_injective
      d4BMPrimitiveSignSumToPrimitivePair_bijective.1
  have hfirst : Summable (f ∘ Sum.inl) :=
    hf.comp_injective Sum.inl_injective
  have hrest : Summable (f ∘ Sum.inr) :=
    hf.comp_injective Sum.inr_injective
  have hpos : Summable ((f ∘ Sum.inr) ∘ Sum.inl) :=
    hrest.comp_injective Sum.inl_injective
  have hneg : Summable ((f ∘ Sum.inr) ∘ Sum.inr) :=
    hrest.comp_injective Sum.inr_injective
  rw [← d4BMPrimitiveSignSumEquivPrimitivePair.tsum_eq
    (fun p : D4BMPrimitiveIntegerPair => d4BMPoincareSeed z P.s p)]
  change (∑' p : D4BMPrimitiveFirstRowPair ⊕
      (D4BMPositivePrimitivePair ⊕ D4BMNegativePrimitivePair),
        f p) = _
  rw [hfirst.tsum_sum hrest]
  have hinner :
      (∑' i : D4BMPositivePrimitivePair ⊕ D4BMNegativePrimitivePair,
          f (Sum.inr i)) =
        (∑' p : D4BMPositivePrimitivePair, f (Sum.inr (Sum.inl p))) +
          ∑' p : D4BMNegativePrimitivePair, f (Sum.inr (Sum.inr p)) := by
    simpa [Function.comp_def] using hpos.tsum_sum hneg
  rw [hinner]
  rfl

theorem d4BM_rawEisensteinPoincareSeries_eq_constant_add_positiveSlices
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMRawEisensteinPoincareSeries z P =
      (z.y : ℂ) ^ P.s +
        ∑' Q : ℕ+,
          d4BMPositivePrimitiveCuspSlice z P (d4BMPositiveModulusOfPNat Q) z.x := by
  unfold d4BMRawEisensteinPoincareSeries
  rw [d4BM_tsum_poincareSeed_sign_decomposition]
  rw [d4BM_tsum_negativePrimitivePair_eq_positive]
  rw [tsum_d4BMPoincareSeed_firstRow]
  rw [d4BM_tsum_positivePrimitiveCuspSlice_eq_positivePrimitivePairs]
  ring

end
end RHTower

