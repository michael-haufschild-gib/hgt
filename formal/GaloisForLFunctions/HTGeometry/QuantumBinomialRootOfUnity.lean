import GaloisForLFunctions.HTGeometry.QuantumTorusPrincipalSymbol
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# The root-of-unity quantum binomial theorem

Gaussian coefficients are defined by their product formula.  Below the primitive order their
denominators are nonzero, and the product formula satisfies the quantum Pascal recurrence.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Numerator of the Gaussian binomial coefficient. -/
def quantumChooseNumerator (q : K) (n k : ℕ) : K :=
  ∏ r ∈ Finset.range k, (1 - q ^ (n - r))

/-- Denominator of the Gaussian binomial coefficient. -/
def quantumChooseDenominator (q : K) (k : ℕ) : K :=
  ∏ r ∈ Finset.range k, (1 - q ^ (r + 1))

/-- Product-form Gaussian binomial coefficient. -/
def quantumChoose (q : K) (n k : ℕ) : K :=
  quantumChooseNumerator q n k / quantumChooseDenominator q k

@[simp]
theorem quantumChoose_zero (q : K) (n : ℕ) :
    quantumChoose q n 0 = 1 := by
  simp [quantumChoose, quantumChooseNumerator, quantumChooseDenominator]

omit [CharZero K] in
theorem quantumChooseNumerator_succ_right (q : K) (n k : ℕ) :
    quantumChooseNumerator q n (k + 1) =
      quantumChooseNumerator q n k * (1 - q ^ (n - k)) := by
  simp [quantumChooseNumerator, Finset.prod_range_succ]

omit [CharZero K] in
theorem quantumChooseDenominator_succ (q : K) (k : ℕ) :
    quantumChooseDenominator q (k + 1) =
      quantumChooseDenominator q k * (1 - q ^ (k + 1)) := by
  simp [quantumChooseDenominator, Finset.prod_range_succ]

omit [CharZero K] in
theorem quantumChooseNumerator_succ_succ
    (q : K) (n k : ℕ) :
    quantumChooseNumerator q (n + 1) (k + 1) =
      (1 - q ^ (n + 1)) * quantumChooseNumerator q n k := by
  have hprod :
      (∏ r ∈ Finset.range k, (1 - q ^ (n + 1 - (r + 1)))) =
        quantumChooseNumerator q n k := by
    unfold quantumChooseNumerator
    apply Finset.prod_congr rfl
    intro r hr
    congr 2
    omega
  unfold quantumChooseNumerator at ⊢
  rw [Finset.prod_range_succ']
  rw [hprod]
  change quantumChooseNumerator q n k * (1 - q ^ (n + 1)) =
    (1 - q ^ (n + 1)) * quantumChooseNumerator q n k
  ring

omit [CharZero K] in
theorem quantumChooseDenominator_ne_zero
    {q : K} {d k : ℕ} (hq : IsPrimitiveRoot q d) (hk : k < d) :
    quantumChooseDenominator q k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro r hr
  have hrk : r < k := by simpa using hr
  have hrpos : r + 1 ≠ 0 := Nat.succ_ne_zero r
  have hrlt : r + 1 < d := lt_of_le_of_lt (Nat.succ_le_iff.mpr hrk) hk
  exact sub_ne_zero.mpr (Ne.symm (hq.pow_ne_one_of_pos_of_lt hrpos hrlt))

omit [CharZero K] in
theorem quantumChoose_step_ne_zero
    {q : K} {d k : ℕ} (hq : IsPrimitiveRoot q d) (hk : k + 1 < d) :
    1 - q ^ (k + 1) ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm
    (hq.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero k) hk))

omit [CharZero K] in
/-- Below the primitive order, product-form Gaussian coefficients satisfy quantum Pascal. -/
theorem quantumChoose_pascal
    {q : K} {d n k : ℕ} (hq : IsPrimitiveRoot q d)
    (hk : k ≤ n) (hkd : k + 1 < d) :
    quantumChoose q (n + 1) (k + 1) =
      quantumChoose q n k + q ^ (k + 1) * quantumChoose q n (k + 1) := by
  have hklt : k < d := lt_of_le_of_lt (Nat.le_succ k) hkd
  have hD := quantumChooseDenominator_ne_zero hq hklt
  have hE := quantumChoose_step_ne_zero hq hkd
  rw [quantumChoose, quantumChoose, quantumChoose,
    quantumChooseNumerator_succ_succ,
    quantumChooseNumerator_succ_right,
    quantumChooseDenominator_succ]
  have hpow : q ^ (k + 1) * q ^ (n - k) = q ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hterm : q ^ (k + 1) * (1 - q ^ (n - k)) =
      q ^ (k + 1) - q ^ (n + 1) := by
    rw [mul_sub, mul_one, hpow]
  field_simp [hD, hE]
  rw [hterm]
  ring

omit [CharZero K] in
/-- Adjacent Gaussian coefficients satisfy the cancellation ratio below the primitive order. -/
theorem quantumChoose_adjacent_ratio
    {q : K} {d n k : ℕ} (hq : IsPrimitiveRoot q d)
    (hkpos : 0 < k) (hkd : k < d) :
    (1 - q ^ k) * quantumChoose q n k =
      (1 - q ^ (n - (k - 1))) * quantumChoose q n (k - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
  have hm : m + 1 < d := by simpa using hkd
  have hm0 : m < d := lt_trans (Nat.lt_succ_self m) hm
  have hD := quantumChooseDenominator_ne_zero hq hm0
  have hE := quantumChoose_step_ne_zero hq hm
  rw [quantumChoose, quantumChoose,
    quantumChooseNumerator_succ_right,
    quantumChooseDenominator_succ]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  field_simp [hD, hE]

omit [CharZero K] in
/-- Every interior coefficient created in the primitive row is zero. -/
theorem quantumChoose_primitive_final_coefficient_zero
    {q : K} {d k : ℕ} (hq : IsPrimitiveRoot q d)
    (hkpos : 0 < k) (hkd : k < d) :
    quantumChoose q (d - 1) (k - 1) +
        q ^ k * quantumChoose q (d - 1) k = 0 := by
  have hkne : 1 - q ^ k ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm
      (hq.pow_ne_one_of_pos_of_lt (Nat.ne_of_gt hkpos) hkd))
  have hratio := quantumChoose_adjacent_ratio hq hkpos hkd (n := d - 1)
  have hqpow : q ^ d = 1 := hq.pow_eq_one
  have hshift : d - 1 - (k - 1) = d - k := by omega
  rw [hshift] at hratio
  have hcancel : q ^ k * (1 - q ^ (d - k)) = -(1 - q ^ k) := by
    have hsum : k + (d - k) = d := Nat.add_sub_of_le (Nat.le_of_lt hkd)
    calc
      q ^ k * (1 - q ^ (d - k)) = q ^ k - q ^ (k + (d - k)) := by
        rw [pow_add]
        ring
      _ = q ^ k - 1 := by rw [hsum, hqpow]
      _ = -(1 - q ^ k) := by ring
  apply (mul_left_cancel₀ hkne)
  rw [mul_zero, mul_add]
  calc
    (1 - q ^ k) * quantumChoose q (d - 1) (k - 1) +
        (1 - q ^ k) * (q ^ k * quantumChoose q (d - 1) k) =
      (1 - q ^ k) * quantumChoose q (d - 1) (k - 1) +
        q ^ k * ((1 - q ^ k) * quantumChoose q (d - 1) k) := by ring
    _ = (1 - q ^ k) * quantumChoose q (d - 1) (k - 1) +
        q ^ k * ((1 - q ^ (d - k)) *
          quantumChoose q (d - 1) (k - 1)) := by rw [hratio]
    _ = ((1 - q ^ k) + q ^ k * (1 - q ^ (d - k))) *
          quantumChoose q (d - 1) (k - 1) := by ring
    _ = 0 := by rw [hcancel]; simp

omit [CharZero K] in
theorem quantumChooseNumerator_self (q : K) :
    ∀ n : ℕ, quantumChooseNumerator q n n = quantumChooseDenominator q n
  | 0 => by simp [quantumChooseNumerator, quantumChooseDenominator]
  | n + 1 => by
      rw [quantumChooseNumerator_succ_succ,
        quantumChooseDenominator_succ, quantumChooseNumerator_self q n]
      ring

omit [CharZero K] in
@[simp]
theorem quantumChoose_self
    {q : K} {d n : ℕ} (hq : IsPrimitiveRoot q d) (hn : n < d) :
    quantumChoose q n n = 1 := by
  rw [quantumChoose, quantumChooseNumerator_self]
  exact div_self (quantumChooseDenominator_ne_zero hq hn)

variable {M : Type*} [AddCommGroup M] [Module K M]

/-- The ordered Gaussian expansion in an endomorphism algebra. -/
def quantumBinomialSum (q : K) (X Y : Module.End K M) (n : ℕ) :
    Module.End K M :=
  ∑ k ∈ Finset.range (n + 1),
    quantumChoose q n k • (Y ^ k * X ^ (n - k))

omit [CharZero K] in
/-- Moving one `X` through `k` copies of `Y` produces the phase `q^k`. -/
theorem quantumCommute_left_pow
    (q : K) (X Y : Module.End K M)
    (hXY : X * Y = q • (Y * X)) :
    ∀ k : ℕ, X * Y ^ k = q ^ k • (Y ^ k * X)
  | 0 => by simp
  | k + 1 => by
      calc
        X * Y ^ (k + 1) = (X * Y ^ k) * Y := by rw [pow_succ, mul_assoc]
        _ = (q ^ k • (Y ^ k * X)) * Y := by rw [quantumCommute_left_pow q X Y hXY k]
        _ = q ^ k • (Y ^ k * (X * Y)) := by simp [mul_assoc]
        _ = q ^ k • (Y ^ k * (q • (Y * X))) := by rw [hXY]
        _ = q ^ (k + 1) • (Y ^ (k + 1) * X) := by
          simp [pow_succ, smul_smul, mul_assoc]

/-- Product-form Gaussian coefficients give the ordered quantum binomial expansion below the
primitive order. -/
theorem quantumBinomial_expansion_of_lt
    {q : K} {d : ℕ} (hq : IsPrimitiveRoot q d)
    (X Y : Module.End K M) (hXY : X * Y = q • (Y * X)) :
    ∀ n : ℕ, n < d → (X + Y) ^ n = quantumBinomialSum q X Y n
  | 0, _ => by simp [quantumBinomialSum]
  | n + 1, hn => by
      have hnlt : n < d := lt_trans (Nat.lt_succ_self n) hn
      have ih := quantumBinomial_expansion_of_lt hq X Y hXY n hnlt
      rw [pow_succ', ih, quantumBinomialSum, add_mul,
        Finset.mul_sum, Finset.mul_sum]
      have hx :
          (∑ k ∈ Finset.range (n + 1),
              X * (quantumChoose q n k • (Y ^ k * X ^ (n - k)))) =
            ∑ k ∈ Finset.range (n + 1),
              (q ^ k * quantumChoose q n k) •
                (Y ^ k * X ^ (n + 1 - k)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.le_of_lt_succ (by simpa using hk)
        calc
          X * (quantumChoose q n k • (Y ^ k * X ^ (n - k))) =
              quantumChoose q n k • (X * (Y ^ k * X ^ (n - k))) := by simp
          _ = quantumChoose q n k •
              ((q ^ k • (Y ^ k * X)) * X ^ (n - k)) := by
                rw [← mul_assoc, quantumCommute_left_pow q X Y hXY k]
          _ = (q ^ k * quantumChoose q n k) •
              (Y ^ k * X ^ (n + 1 - k)) := by
                rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ']
                simp [smul_smul, mul_assoc]
                congr 1
                ring
      have hy :
          (∑ k ∈ Finset.range (n + 1),
              Y * (quantumChoose q n k • (Y ^ k * X ^ (n - k)))) =
            ∑ k ∈ Finset.range (n + 1),
              quantumChoose q n k •
                (Y ^ (k + 1) * X ^ (n + 1 - (k + 1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.le_of_lt_succ (by simpa using hk)
        rw [show n + 1 - (k + 1) = n - k by omega, pow_succ']
        simp [mul_assoc]
      have hinner :
          (∑ k ∈ Finset.range n,
              ((q ^ (k + 1) * quantumChoose q n (k + 1)) •
                  (Y ^ (k + 1) * X ^ (n + 1 - (k + 1))) +
                quantumChoose q n k •
                  (Y ^ (k + 1) * X ^ (n + 1 - (k + 1))))) =
            ∑ k ∈ Finset.range n,
              quantumChoose q (n + 1) (k + 1) •
                (Y ^ (k + 1) * X ^ (n + 1 - (k + 1))) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k < n := by simpa using hk
        rw [quantumChoose_pascal hq (Nat.le_of_lt hkn) (by omega)]
        module
      let sx : Module.End K M := ∑ k ∈ Finset.range n,
        (q ^ (k + 1) * quantumChoose q n (k + 1)) •
          (Y ^ (k + 1) * X ^ (n + 1 - (k + 1)))
      let sy : Module.End K M := ∑ k ∈ Finset.range n,
        quantumChoose q n k •
          (Y ^ (k + 1) * X ^ (n + 1 - (k + 1)))
      let sr : Module.End K M := ∑ k ∈ Finset.range n,
        quantumChoose q (n + 1) (k + 1) •
          (Y ^ (k + 1) * X ^ (n + 1 - (k + 1)))
      have hcombine : sx + sy = sr := by
        dsimp [sx, sy, sr]
        rw [← Finset.sum_add_distrib]
        exact hinner
      let x0 : Module.End K M :=
        (q ^ 0 * quantumChoose q n 0) • (Y ^ 0 * X ^ (n + 1 - 0))
      let yn : Module.End K M :=
        quantumChoose q n n • (Y ^ (n + 1) * X ^ (n + 1 - (n + 1)))
      let rn : Module.End K M :=
        quantumChoose q (n + 1) (n + 1) •
          (Y ^ (n + 1) * X ^ (n + 1 - (n + 1)))
      let r0 : Module.End K M :=
        quantumChoose q (n + 1) 0 • (Y ^ 0 * X ^ (n + 1 - 0))
      have hx0 : x0 = X ^ (n + 1) := by simp [x0]
      have hyn : yn = Y ^ (n + 1) := by
        simp [yn, quantumChoose_self hq hnlt]
      have hrn : rn = Y ^ (n + 1) := by
        simp [rn, quantumChoose_self hq hn]
      have hr0 : r0 = X ^ (n + 1) := by simp [r0]
      rw [hx, hy]
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      unfold quantumBinomialSum
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      change sx + x0 + (sy + yn) = sr + rn + r0
      rw [show sx + x0 + (sy + yn) = (sx + sy) + x0 + yn by abel,
        hcombine, hx0, hyn, hrn, hr0]
      abel

/-- **Root-of-unity quantum freshman's dream.** -/
theorem quantumBinomial_pow_primitive
    {q : K} {d : ℕ} (hq : IsPrimitiveRoot q d) (hd : 0 < d)
    (X Y : Module.End K M) (hXY : X * Y = q • (Y * X)) :
    (X + Y) ^ d = X ^ d + Y ^ d := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hdpos : 0 < d + 1 := Nat.succ_pos d
  have hdlt : d < d + 1 := Nat.lt_succ_self d
  have hexp := quantumBinomial_expansion_of_lt hq X Y hXY d hdlt
  rw [pow_succ', hexp, quantumBinomialSum, add_mul,
    Finset.mul_sum, Finset.mul_sum]
  have hx :
      (∑ k ∈ Finset.range (d + 1),
          X * (quantumChoose q d k • (Y ^ k * X ^ (d - k)))) =
        ∑ k ∈ Finset.range (d + 1),
          (q ^ k * quantumChoose q d k) •
            (Y ^ k * X ^ (d + 1 - k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkd : k ≤ d := Nat.le_of_lt_succ (by simpa using hk)
    calc
      X * (quantumChoose q d k • (Y ^ k * X ^ (d - k))) =
          quantumChoose q d k • (X * (Y ^ k * X ^ (d - k))) := by simp
      _ = quantumChoose q d k •
          ((q ^ k • (Y ^ k * X)) * X ^ (d - k)) := by
            rw [← mul_assoc, quantumCommute_left_pow q X Y hXY k]
      _ = (q ^ k * quantumChoose q d k) •
          (Y ^ k * X ^ (d + 1 - k)) := by
            rw [show d + 1 - k = (d - k) + 1 by omega, pow_succ']
            simp [smul_smul, mul_assoc]
            congr 1
            ring
  have hy :
      (∑ k ∈ Finset.range (d + 1),
          Y * (quantumChoose q d k • (Y ^ k * X ^ (d - k)))) =
        ∑ k ∈ Finset.range (d + 1),
          quantumChoose q d k •
            (Y ^ (k + 1) * X ^ (d + 1 - (k + 1))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkd : k ≤ d := Nat.le_of_lt_succ (by simpa using hk)
    rw [show d + 1 - (k + 1) = d - k by omega, pow_succ']
    simp [mul_assoc]
  rw [hx, hy, Finset.sum_range_succ', Finset.sum_range_succ]
  have hmid :
      (∑ k ∈ Finset.range d,
          ((q ^ (k + 1) * quantumChoose q d (k + 1)) •
              (Y ^ (k + 1) * X ^ (d + 1 - (k + 1))) +
            quantumChoose q d k •
              (Y ^ (k + 1) * X ^ (d + 1 - (k + 1))))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < d := by simpa using hk
    rw [← add_smul]
    have hz := quantumChoose_primitive_final_coefficient_zero hq
      (Nat.succ_pos k) (by omega)
    simpa [add_comm, add_left_comm, add_assoc] using congrArg
      (fun c : K ↦ c • (Y ^ (k + 1) * X ^ (d + 1 - (k + 1)))) hz
  let sx : Module.End K M := ∑ k ∈ Finset.range d,
    (q ^ (k + 1) * quantumChoose q d (k + 1)) •
      (Y ^ (k + 1) * X ^ (d + 1 - (k + 1)))
  let sy : Module.End K M := ∑ k ∈ Finset.range d,
    quantumChoose q d k •
      (Y ^ (k + 1) * X ^ (d + 1 - (k + 1)))
  have hcombine : sx + sy = 0 := by
    dsimp [sx, sy]
    rw [← Finset.sum_add_distrib]
    exact hmid
  let x0 : Module.End K M :=
    (q ^ 0 * quantumChoose q d 0) • (Y ^ 0 * X ^ (d + 1 - 0))
  let yd : Module.End K M :=
    quantumChoose q d d • (Y ^ (d + 1) * X ^ (d + 1 - (d + 1)))
  have hx0 : x0 = X ^ (d + 1) := by simp [x0]
  have hyd : yd = Y ^ (d + 1) := by
    simp [yd, quantumChoose_self hq hdlt]
  change sx + x0 + (sy + yd) = X ^ (d + 1) + Y ^ (d + 1)
  rw [show sx + x0 + (sy + yd) = (sx + sy) + x0 + yd by abel,
    hcombine, zero_add, hx0, hyd]

omit [CharZero K] in
/-- A generator that `q`-commutes with every entry of a finite list also `q`-commutes with
the list sum.  This is the additive closure needed to pass from the binary quantum binomial
law to an arbitrary finite horizon. -/
theorem quantumCommute_list_sum
    (q : K) (X : Module.End K M) :
    ∀ L : List (Module.End K M),
      (∀ Y ∈ L, X * Y = q • (Y * X)) →
        X * L.sum = q • (L.sum * X)
  | [], _ => by simp
  | Y :: L, h => by
      have hY : X * Y = q • (Y * X) := h Y (by simp)
      have hL : ∀ Z ∈ L, X * Z = q • (Z * X) := by
        intro Z hZ
        exact h Z (by simp [hZ])
      rw [List.sum_cons, mul_add, add_mul, smul_add, hY,
        quantumCommute_list_sum q X L hL]

/-- **Finite root-of-unity quantum multinomial theorem.**  An ordered list of pairwise
`q`-commuting endomorphisms has no mixed terms in its primitive-order power. -/
theorem quantumMultinomial_list_pow_primitive
    {q : K} {d : ℕ} (hq : IsPrimitiveRoot q d) (hd : 0 < d) :
    ∀ L : List (Module.End K M),
      L.Pairwise (fun X Y ↦ X * Y = q • (Y * X)) →
        L.sum ^ d = (L.map (fun X ↦ X ^ d)).sum
  | [], _ => by simp [Nat.ne_of_gt hd]
  | X :: L, hpair => by
      have hhead : ∀ Y ∈ L, X * Y = q • (Y * X) :=
        (List.pairwise_cons.mp hpair).1
      have htail : L.Pairwise (fun Y Z ↦ Y * Z = q • (Z * Y)) :=
        (List.pairwise_cons.mp hpair).2
      rw [List.sum_cons, List.map_cons, List.sum_cons,
        quantumBinomial_pow_primitive hq hd X L.sum
          (quantumCommute_list_sum q X L hhead),
        quantumMultinomial_list_pow_primitive hq hd L htail]

/-- Finite-family form of the root-of-unity quantum multinomial theorem. -/
theorem quantumMultinomial_fin_pow_primitive
    {q : K} {d n : ℕ} (hq : IsPrimitiveRoot q d) (hd : 0 < d)
    (X : Fin n → Module.End K M)
    (hX : ∀ i j, i < j → X i * X j = q • (X j * X i)) :
    (∑ i, X i) ^ d = ∑ i, X i ^ d := by
  have hpair : (List.ofFn X).Pairwise
      (fun Y Z ↦ Y * Z = q • (Z * Y)) := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact hX i j hij
  simpa [List.sum_ofFn] using
    (quantumMultinomial_list_pow_primitive hq hd (List.ofFn X) hpair)

/-- Scalar-weighted finite-family form.  The degree-`d` scalar coefficients themselves acquire
degree `d`, while every mixed quantum word cancels. -/
theorem quantumMultinomial_fin_smul_pow_primitive
    {q : K} {d n : ℕ} (hq : IsPrimitiveRoot q d) (hd : 0 < d)
    (G : Fin n → Module.End K M) (c : Fin n → K)
    (hG : ∀ i j, i < j → G i * G j = q • (G j * G i)) :
    (∑ i, c i • G i) ^ d = ∑ i, c i ^ d • G i ^ d := by
  rw [quantumMultinomial_fin_pow_primitive hq hd
    (fun i ↦ c i • G i)]
  · apply Finset.sum_congr rfl
    intro i _
    exact smul_pow (c i) (G i) d
  · intro i j hij
    rw [smul_mul_smul, hG i j hij, smul_mul_smul]
    simp only [smul_smul]
    congr 1
    ring

end

end GaloisForLFunctions.HTGeometry
