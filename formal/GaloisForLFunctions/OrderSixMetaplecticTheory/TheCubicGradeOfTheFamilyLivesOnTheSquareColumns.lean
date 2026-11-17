import GaloisForLFunctions.OrderSixMetaplecticTheory.TheWeilIndexIsAKleinCombination
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicTwistAtTwoOfTheThetaSquareHasADoublePole

/-!
# The cubic grade of the family lives on the square columns

Column `n` of the order-six family is the Klein combination of the layers twisted by
`Ξ_{s,n} = \overline{r(n, ·)κ_sχ₂(·/n)₃(·/n)₂}` (`columnSeries_eq_klein`). On classes prime to `2n` the cube of a layer
character forgets every cubic factor (`layerTwist_cube`):

`Ξ_{s,n}(c)³ = r(n, c)κ_s(c)(c/n)₂`,

a sign. A layer is in the cubic grade (`Ξ³ = 1`, cube factor `Z₀`, double pole possible) or in the quadratic grade
(`Ξ³` a nontrivial quadratic character, cube factor an entire Hecke `L`-function, at most a simple pole). Which one is
decided by the column:

* at a square column `n = m²` the Klein-trivial layer is cubic (`square_cubicLayer_cube`: `r(m², ·) = r(m, ·)² = 1`,
  `(·/m²)₂ = 1`) and the three Klein layers are quadratic (`square_kleinLayer_quadratic`);
* at a column with an odd power of a prime `π` every layer is quadratic (`nonsquare_layer_quadratic`): a class
  `c ≡ 1 mod 12n'` that is a non-residue modulo `π` has `Ξ(c)³ = (c/π)₂^e = −1`.

**The cubic grade of the family — the only grade whose main terms are double poles, reached by the traces —
lives exactly on the square columns, in the Klein-trivial layer.** Every other layer of every column carries its main term
in a simple pole of the quadratic grade.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open FamilyContinuationTheory MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.Eisenstein.Coordinates MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi SpectralTheoryOfTheCubicCover

/-! ### Klein characters modulo four -/

theorem kleinChar_congr (k : ZMod 4 → ZMod 4 → ℤ) (h1 : k 1 0 = 1)
    (hk : ∀ a b c d : ZMod 4, oddCoord a b → oddCoord c d → k (mulFst a b c d) (mulSnd a b c d) = k a b * k c d)
    {c d : O} (h : (4 : O) ∣ c - d) : kleinChar k h1 hk c = kleinChar k h1 hk d := by
  have h2cd : c ∈ Ideal.span {(2 : O)} ↔ d ∈ Ideal.span {(2 : O)} := by
    have h24 : (2 : O) ∣ c - d := (dvd_trans ⟨2, by norm_num⟩ h)
    simp only [Ideal.mem_span_singleton]
    constructor
    · intro hc
      simpa using dvd_sub hc h24
    · intro hd
      simpa using dvd_add hd h24
  obtain ⟨a, b, rfl⟩ := exists_eval c
  obtain ⟨e, he⟩ := h
  obtain ⟨a', b', rfl⟩ := exists_eval e
  have hd : d = eval (a - 4 * a') (b - 4 * b') := by
    simp only [eval] at he ⊢
    push_cast
    linear_combination -he
  by_cases hc : eval a b ∈ Ideal.span {(2 : O)}
  · have hd2 : d ∈ Ideal.span {(2 : O)} := h2cd.mp hc
    change (if eval a b ∈ Ideal.span {(2 : O)} then 0 else _) = (if d ∈ Ideal.span {(2 : O)} then 0 else _)
    rw [if_pos hc, if_pos hd2]
  · have hd2 : eval (a - 4 * a') (b - 4 * b') ∉ Ideal.span {(2 : O)} := by
      rw [← hd]
      exact fun h' => hc (h2cd.mpr h')
    have h4 : ((4 : ℤ) : ZMod 4) = 0 := rfl
    rw [hd, kleinChar_eval _ _ _ a b hc, kleinChar_eval _ _ _ _ _ hd2]
    simp only [Int.cast_sub, Int.cast_mul, h4, zero_mul, sub_zero]

/-- The Klein characters `1, κ₁, κ_{ω²}, κ_ω` of the four layers. -/
def kleinBase : Fin 4 → O →* ℂ := ![kleinZero, kleinOne, kleinOmegaSq, kleinOmega]

theorem kleinFactor_eq (n : O) (hn : n ∉ Ideal.span {(2 : O)}) (i : Fin 4) :
    kleinFactor n hn i = phaseTwist n hn * kleinBase i * cubicTwoHom := by
  fin_cases i <;> rfl

theorem kleinBase_congr (i : Fin 4) {c d : O} (h : (4 : O) ∣ c - d) : kleinBase i c = kleinBase i d := by
  fin_cases i
  · show kleinZero c = kleinZero d
    unfold kleinZero
    exact kleinChar_congr _ _ _ h
  · show kleinOne c = kleinOne d
    unfold kleinOne
    exact kleinChar_congr _ _ _ h
  · show kleinOmegaSq c = kleinOmegaSq d
    unfold kleinOmegaSq
    exact kleinChar_congr _ _ _ h
  · show kleinOmega c = kleinOmega d
    unfold kleinOmega
    exact kleinChar_congr _ _ _ h

theorem kleinBase_sq (i : Fin 4) (c : O) (hc : c ∉ Ideal.span {(2 : O)}) : kleinBase i c ^ 2 = 1 := by
  obtain ⟨a, b, rfl⟩ := exists_eval c
  fin_cases i
  · show kleinZero (eval a b) ^ 2 = 1
    unfold kleinZero
    rw [kleinChar_eval _ _ _ a b hc]
    simp [oddZ]
  · change kleinOne (eval a b) ^ 2 = 1
    rw [kleinOne, kleinChar_eval _ _ _ a b hc]
    rcases kleinOneZ_sign (a : ZMod 4) (b : ZMod 4) with h | h <;> rw [h] <;> norm_num
  · change kleinOmegaSq (eval a b) ^ 2 = 1
    rw [kleinOmegaSq, kleinChar_eval _ _ _ a b hc]
    rcases kleinOmegaSqZ_sign (a : ZMod 4) (b : ZMod 4) with h | h <;> rw [h] <;> norm_num
  · change kleinOmega (eval a b) ^ 2 = 1
    rw [kleinOmega, kleinChar_eval _ _ _ a b hc]
    rcases kleinOmegaZ_sign (a : ZMod 4) (b : ZMod 4) with h | h <;> rw [h] <;> norm_num

/-- Every nontrivial Klein character takes the value `−1` on an odd class. -/
theorem exists_kleinBase_neg (i : Fin 4) (hi : i ≠ 0) :
    ∃ c₀ : O, c₀ ∉ Ideal.span {(2 : O)} ∧ kleinBase i c₀ = -1 := by
  fin_cases i
  · exact absurd rfl hi
  · refine ⟨eval 1 2, not_mem_of_oddCoord 1 2 (by decide), ?_⟩
    change kleinOne (eval 1 2) = -1
    rw [kleinOne, kleinChar_eval _ _ _ 1 2 (not_mem_of_oddCoord 1 2 (by decide))]
    have : kleinOneZ ((1 : ℤ) : ZMod 4) ((2 : ℤ) : ZMod 4) = -1 := by decide
    rw [this]
    norm_num
  · refine ⟨eval (-1) 0, not_mem_of_oddCoord (-1) 0 (by decide), ?_⟩
    change kleinOmegaSq (eval (-1) 0) = -1
    rw [kleinOmegaSq, kleinChar_eval _ _ _ (-1) 0 (not_mem_of_oddCoord (-1) 0 (by decide))]
    have : kleinOmegaSqZ ((-1 : ℤ) : ZMod 4) ((0 : ℤ) : ZMod 4) = -1 := by decide
    rw [this]
    norm_num
  · refine ⟨eval (-1) 0, not_mem_of_oddCoord (-1) 0 (by decide), ?_⟩
    change kleinOmega (eval (-1) 0) = -1
    rw [kleinOmega, kleinChar_eval _ _ _ (-1) 0 (not_mem_of_oddCoord (-1) 0 (by decide))]
    have : kleinOmegaZ ((-1 : ℤ) : ZMod 4) ((0 : ℤ) : ZMod 4) = -1 := by decide
    rw [this]
    norm_num

/-! ### The cube of a layer character -/

theorem star_eq_of_sq_eq_one {x : ℂ} (h : x ^ 2 = 1) : star x = x := by
  rcases sq_eq_one_iff.mp h with rfl | rfl <;> simp

theorem phaseTwist_apply_odd (n : O) (hn : n ∉ Ideal.span {(2 : O)}) {c : O} (hc : c ∉ Ideal.span {(2 : O)}) :
    phaseTwist n hn c = star (quadraticPhase n c) := by
  change (if c ∈ Ideal.span {(2 : O)} then 0 else star (quadraticPhase n c)) = _
  rw [if_neg hc]

/-- **The cube of a layer character is a sign:** `Ξ_{s,n}(c)³ = r(n, c)κ_s(c)(c/n)₂` on classes prime to `2n`. -/
theorem layerTwist_cube (n : O) (hn : lambda ^ 2 ∣ n - 1) (hn0 : n ≠ 0) (hn2 : IsCoprime n 2) (i : Fin 4) (c : O)
    (hc : c ∉ Ideal.span {(2 : O)}) (hcn : IsCoprime c n) :
    (layerTwist (kleinFactor n (not_mem_two_of_isCoprime hn2) i) n hn hn0 hn2 c) ^ 3 =
      quadraticPhase n c * kleinBase i c * quadSymbol c n := by
  have hnodd := not_mem_two_of_isCoprime hn2
  have hq := quadraticPhase_sq hnodd hc
  have hk := kleinBase_sq i c hc
  have hs := quadSymbol_sq hn0 hn2 hcn
  have hc2 : IsCoprime c (-2) :=
    ((Prime.coprime_iff_not_dvd two_prime).mpr (fun hd => hc (Ideal.mem_span_singleton.mpr hd))).symm.neg_right
  have h3 : ringComplex (symbol c (-2)) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime c (-2) primary_neg_two hc2, map_one]
  have h3n : ringComplex (symbol c n) ^ 3 = 1 := by
    rw [← map_pow, symbol_cube_of_isCoprime c n hn hcn, map_one]
  have hcube2 : cubicTwoHom c = ringComplex (symbol c (-2)) ^ 2 := rfl
  have hkstar := star_eq_of_sq_eq_one hk
  have hsstar := star_eq_of_sq_eq_one hs
  have hq3 : quadraticPhase n c ^ 3 = quadraticPhase n c := by
    rw [pow_succ, hq, one_mul]
  have hk3 : kleinBase i c ^ 3 = kleinBase i c := by rw [pow_succ, hk, one_mul]
  have hs3 : quadSymbol c n ^ 3 = quadSymbol c n := by rw [pow_succ, hs, one_mul]
  have e : (star (quadraticPhase n c) * kleinBase i c * ringComplex (symbol c (-2)) ^ 2 *
      (ringComplex (symbol c n) * quadSymbol c n)) ^ 3 =
      star (quadraticPhase n c) ^ 3 * kleinBase i c ^ 3 * (ringComplex (symbol c (-2)) ^ 3) ^ 2 *
        ringComplex (symbol c n) ^ 3 * quadSymbol c n ^ 3 := by ring
  rw [layerTwist_apply, kleinFactor_eq, MonoidHom.mul_apply, MonoidHom.mul_apply, phaseTwist_apply_odd n hnodd hc,
    hcube2, ← star_pow, e, h3, h3n, one_pow, mul_one, mul_one, hk3, hs3, ← star_pow, hq3, star_mul', star_mul',
    star_star, hkstar, hsstar]

/-! ### Square columns -/

/-- **At a square column the Klein-trivial layer is in the cubic grade.** -/
theorem square_cubicLayer_cube (m : O) (hm : lambda ^ 2 ∣ m - 1) (hm0 : m ≠ 0) (hm2 : IsCoprime m 2)
    (c : O) (hc : c ∉ Ideal.span {(2 : O)}) (hcm : IsCoprime c m) :
    (layerTwist (kleinFactor (m * m) (not_mem_two_of_isCoprime (hm2.mul_left hm2)) 0) (m * m)
      (by have := dvd_add (dvd_mul_of_dvd_left hm m) hm; convert this using 1; ring) (mul_ne_zero hm0 hm0)
        (hm2.mul_left hm2) c) ^ 3 = 1 := by
  have hmodd := not_mem_two_of_isCoprime hm2
  rw [layerTwist_cube (m * m) _ (mul_ne_zero hm0 hm0) (hm2.mul_left hm2) 0 c hc (hcm.mul_right hcm),
    quadraticPhase_mul_left hmodd hmodd hc, quadSymbol_mul_denominator]
  have hk : kleinBase 0 c = 1 := by
    obtain ⟨a, b, rfl⟩ := exists_eval c
    show kleinZero (eval a b) = 1
    unfold kleinZero
    rw [kleinChar_eval _ _ _ a b hc]
    simp [oddZ]
  rw [hk, ← sq, ← sq, quadraticPhase_sq hmodd hc, quadSymbol_sq hm0 hm2 hcm]
  ring

theorem isCoprime_four_three_mul (m : O) (hm2 : IsCoprime m 2) :
    IsCoprime (4 : O) (3 * m) := by
  have h43 : IsCoprime (4 : O) 3 := ⟨1, -1, by norm_num⟩
  have h4m : IsCoprime (4 : O) m := by
    have := hm2.pow_right (n := 2)
    norm_num at this
    exact this.symm
  exact h43.mul_right h4m

/-- **At a square column the three Klein layers are in the quadratic grade.** -/
theorem square_kleinLayer_quadratic (m : O) (hm : lambda ^ 2 ∣ m - 1) (hm0 : m ≠ 0) (hm2 : IsCoprime m 2)
    (i : Fin 4) (hi : i ≠ 0) :
    ∃ c : O, lambda ^ 2 ∣ c - 1 ∧ c ∉ Ideal.span {(2 : O)} ∧ IsCoprime c (m * m) ∧
      (layerTwist (kleinFactor (m * m) (not_mem_two_of_isCoprime (hm2.mul_left hm2)) i) (m * m)
        (by have := dvd_add (dvd_mul_of_dvd_left hm m) hm; convert this using 1; ring) (mul_ne_zero hm0 hm0)
          (hm2.mul_left hm2) c) ^ 3 = -1 := by
  have hmodd := not_mem_two_of_isCoprime hm2
  obtain ⟨c₀, hc₀, hk₀⟩ := exists_kleinBase_neg i hi
  obtain ⟨u, v, huv⟩ := isCoprime_four_three_mul m hm2
  set c := c₀ + 4 * (u * (1 - c₀)) with hcdef
  have h4 : (4 : O) ∣ c - c₀ := ⟨u * (1 - c₀), by rw [hcdef]; ring⟩
  have hM : 3 * m ∣ c - 1 := ⟨v * (c₀ - 1), by rw [hcdef]; linear_combination (1 - c₀) * huv⟩
  have hc3 : (3 : O) ∣ c - 1 := (dvd_mul_right 3 m).trans hM
  have hcm1 : m ∣ c - 1 := (dvd_mul_left m 3).trans hM
  have hcodd : c ∉ Ideal.span {(2 : O)} := by
    intro h
    apply hc₀
    rw [Ideal.mem_span_singleton] at h ⊢
    have h2 : (2 : O) ∣ c - c₀ := dvd_trans ⟨2, by norm_num⟩ h4
    simpa using dvd_sub h h2
  have hcm : IsCoprime c m := by
    obtain ⟨t, ht⟩ := hcm1
    exact ⟨1, -t, by linear_combination ht⟩
  refine ⟨c, lambda_sq_dvd_three.trans hc3, hcodd, hcm.mul_right hcm, ?_⟩
  rw [layerTwist_cube (m * m) _ (mul_ne_zero hm0 hm0) (hm2.mul_left hm2) i c hcodd (hcm.mul_right hcm),
    quadraticPhase_mul_left hmodd hmodd hcodd, quadSymbol_mul_denominator, ← sq, ← sq, quadraticPhase_sq hmodd hcodd, quadSymbol_sq hm0 hm2 hcm,
    kleinBase_congr i h4, hk₀]
  ring

/-! ### Columns with an odd prime power -/

theorem quadIdealSymbol_congr (I : Ideal O) {x y : O} (h : x - y ∈ I) : quadIdealSymbol I x = quadIdealSymbol I y := by
  unfold quadIdealSymbol
  split_ifs with hI
  · rfl
  · congr 1
    refine Multiset.map_congr rfl fun P hP => ?_
    have hle : I ≤ P := Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP)
    have hxy : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.mpr (hle h)
    unfold quadPrimeValue
    split_ifs with hg
    · rw [hxy]
    · rfl

theorem quadSymbol_pow_denominator (x y : O) (e : ℕ) : quadSymbol x (y ^ e) = quadSymbol x y ^ e := by
  induction e with
  | zero => rw [pow_zero, pow_zero, quadSymbol_one_denominator]
  | succ k ih => rw [pow_succ, pow_succ, quadSymbol_mul_denominator, ih]

/-- **A column with an odd power of a prime has every layer in the quadratic grade.** If `n = π^e n'` with `e` odd and
`π ∤ n'`, then for every Klein layer there is a primary class `c` prime to `2n` with `Ξ(c)³ = −1`. -/
theorem nonsquare_layer_quadratic (P : PrimaryPrime) (hP2 : IsCoprime P.p 2) (e : ℕ) (he : Odd e) (n' : O)
    (hn'0 : n' ≠ 0) (hn'2 : IsCoprime n' 2) (hpn' : ¬ P.p ∣ n') (hn : lambda ^ 2 ∣ P.p ^ e * n' - 1)
    (i : Fin 4) :
    ∃ c : O, lambda ^ 2 ∣ c - 1 ∧ c ∉ Ideal.span {(2 : O)} ∧ IsCoprime c (P.p ^ e * n') ∧
      (layerTwist (kleinFactor (P.p ^ e * n') (not_mem_two_of_isCoprime ((hP2.pow_left).mul_left hn'2)) i)
        (P.p ^ e * n') hn (mul_ne_zero (pow_ne_zero e P.ne_zero) hn'0) ((hP2.pow_left).mul_left hn'2) c) ^ 3 = -1 := by
  set n := P.p ^ e * n' with hndef
  have hn2 : IsCoprime n 2 := (hP2.pow_left).mul_left hn'2
  have hnodd := not_mem_two_of_isCoprime hn2
  have hn0 : n ≠ 0 := mul_ne_zero (pow_ne_zero e P.ne_zero) hn'0
  haveI hmax : (Ideal.span {P.p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible P.prime.irreducible
  have h2P : (2 : O) ∉ Ideal.span {P.p} := fun h =>
    P.prime.not_unit (hP2.isUnit_of_dvd' (dvd_refl _) (Ideal.mem_span_singleton.mp h))
  have hchar : ringChar (O ⧸ Ideal.span {P.p}) ≠ 2 := by
    intro hc
    apply h2P
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := ringChar.spec (O ⧸ Ideal.span {P.p}) 2
    rw [hc] at this
    rw [map_ofNat]
    simpa using this.mpr (dvd_refl 2)
  obtain ⟨ν₀, hν₀⟩ := quadraticChar_exists_neg_one hchar
  obtain ⟨ν, rfl⟩ := Ideal.Quotient.mk_surjective ν₀
  have h12 : IsCoprime (12 * n') P.p := by
    have h3 : IsCoprime (3 : O) P.p := P.isCoprime_three
    have h4 : IsCoprime (4 : O) P.p := by
      have := hP2.symm.pow_left (m := 2)
      norm_num at this
      exact this
    have hn'p : IsCoprime n' P.p := ((Prime.coprime_iff_not_dvd P.prime).mpr hpn').symm
    have : (12 : O) = 4 * 3 := by norm_num
    rw [this]
    exact (h4.mul_left h3).mul_left hn'p
  obtain ⟨u, v, huv⟩ := h12
  set c := 1 + 12 * n' * (u * (ν - 1)) with hcdef
  have hcν : P.p ∣ c - ν := ⟨-(v * (ν - 1)), by rw [hcdef]; linear_combination (ν - 1) * huv⟩
  have h12c : 12 * n' ∣ c - 1 := ⟨u * (ν - 1), by rw [hcdef]; ring⟩
  have h4c : (4 : O) ∣ c - 1 := (dvd_mul_of_dvd_left (show (4 : O) ∣ 12 from ⟨3, by norm_num⟩) n').trans h12c
  have h3c : (3 : O) ∣ c - 1 := (dvd_mul_of_dvd_left (show (3 : O) ∣ 12 from ⟨4, by norm_num⟩) n').trans h12c
  have hn'c : n' ∣ c - 1 := (dvd_mul_left n' 12).trans h12c
  have hcodd : c ∉ Ideal.span {(2 : O)} := by
    intro h
    rw [Ideal.mem_span_singleton] at h
    have h2 : (2 : O) ∣ c - 1 := dvd_trans ⟨2, by norm_num⟩ h4c
    have : (2 : O) ∣ 1 := by simpa using dvd_sub h h2
    exact two_not_isUnit (isUnit_of_dvd_one this)
  have hres : Ideal.Quotient.mk (Ideal.span {P.p}) c = Ideal.Quotient.mk (Ideal.span {P.p}) ν :=
    Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr hcν)
  have hνne : Ideal.Quotient.mk (Ideal.span {P.p}) ν ≠ 0 := by
    intro h0
    rw [h0, quadraticChar_zero] at hν₀
    norm_num at hν₀
  have hcp : IsCoprime c P.p := by
    refine ((Prime.coprime_iff_not_dvd P.prime).mpr fun hd => hνne ?_).symm
    rw [← hres, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hd
  have hcn' : IsCoprime c n' := by
    obtain ⟨t, ht⟩ := hn'c
    exact ⟨1, -t, by linear_combination ht⟩
  have hcn : IsCoprime c n := (hcp.pow_right).mul_right hcn'
  refine ⟨c, lambda_sq_dvd_three.trans h3c, hcodd, hcn, ?_⟩
  rw [layerTwist_cube n hn hn0 hn2 i c hcodd hcn]
  have hq : quadraticPhase n c = 1 := by
    have hnc : (4 : O) ∣ n * c - n * 1 := by rw [← mul_sub]; exact dvd_mul_of_dvd_right h4c n
    unfold quadraticPhase
    rw [fixedDualAverage_congr hnc, fixedDualAverage_congr h4c, mul_one, fixedDualAverage_one, mul_one,
      div_self (gamma_ne_zero hnodd)]
  have hk : kleinBase i c = 1 := by rw [kleinBase_congr i h4c, map_one]
  have hπ : quadSymbol c P.p = -1 := by
    rw [quadSymbol_prime P.p h2P, hres]
    simp [complexQuadraticChar, hν₀]
  have hn'1 : quadSymbol c n' = 1 := by
    have := quadIdealSymbol_congr (Ideal.span {n'}) (Ideal.mem_span_singleton.mpr hn'c)
    change quadIdealSymbol (Ideal.span {n'}) c = 1
    rw [this]
    exact quadSymbol_one_numerator hn'0 hn'2
  rw [hq, hk, hndef, quadSymbol_mul_denominator, quadSymbol_pow_denominator, hπ, hn'1, he.neg_one_pow]
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
