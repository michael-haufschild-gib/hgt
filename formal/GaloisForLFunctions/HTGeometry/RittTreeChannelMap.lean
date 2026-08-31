import GaloisForLFunctions.HTGeometry.RatFuncChainRule
import GaloisForLFunctions.HTGeometry.RittCyclicNoCocycleTwo

/-!
# The tree channel map is a cyclic normal form

The homogeneous belief-propagation map of a `p`-ary tree with two affine channel weights is

`R(y) = ((1+uy)^p − (1+vy)^p) / ((1+uy)^p + (1+vy)^p)`.

The Möbius coordinate `Φ(t) = (t−1)/(u − vt)` conjugates the cyclic normal form

`h = (A − Bλ t^p)/(1 − λ t^p)`,   `A = (1−u)/(1−v)`,  `B = (1+u)/(1+v)`,  `λ = (1+v)/(v−1)`,

to `R`: both `Φ ∘ h` and `R ∘ Φ` equal the symmetric form `(t^p − 1)/(t^p + 1)`.  Indeed
`1 + uΦ = (u−v)t/(u−vt)` and `1 + vΦ = (u−v)/(u−vt)`, so the two branch weights become `t` and `1`
up to a common factor; and on the other side the numerator and denominator of `Φ ∘ h` are both
`(u−v)/(1−v)` times `t^p ∓ 1`.

So the transport of an invariant differential through the conjugacy turns a Ritt cocycle for the
channel map into one for the normal form, which has none.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable section

/-- Numerator of the tree channel map. -/
def treeNum (p : ℕ) (u v : K) : K[X] := (1 + C u * X) ^ p - (1 + C v * X) ^ p

/-- Denominator of the tree channel map. -/
def treeDen (p : ℕ) (u v : K) : K[X] := (1 + C u * X) ^ p + (1 + C v * X) ^ p

/-- **The homogeneous tree channel map.** -/
def treeRG (p : ℕ) (u v : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (treeNum p u v) / algebraMap K[X] (RatFunc K) (treeDen p u v)

/-- The conjugating Möbius coordinate. -/
def treeConj (u v : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (X - 1) / algebraMap K[X] (RatFunc K) (C u - C v * X)

/-- The two critical values and the pole parameter of the conjugated map. -/
def treeA (u v : K) : K := (1 - u) / (1 - v)

def treeB (u v : K) : K := (1 + u) / (1 + v)

def treeLam (v : K) : K := (1 + v) / (v - 1)

omit [CharZero K] in
theorem treeConjDen_ne_zero {u v : K} (huv : u ≠ v) : (C u - C v * X : K[X]) ≠ 0 := by
  intro h
  have h1 := congrArg (Polynomial.eval 1) h
  have h0 := congrArg (Polynomial.eval 0) h
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_zero, mul_one, mul_zero, sub_zero] at h1 h0
  exact huv (by linear_combination h1 + h0 - h0)

omit [CharZero K] in
/-- The symmetric form `(t^p − 1)/(t^p + 1)` is the normal form with parameters `−1, 1, −1`. -/
theorem cnf_symmetric (p : ℕ) :
    cnf p (-1 : K) 1 (-1)
      = algebraMap K[X] (RatFunc K) (X ^ p - 1)
        / algebraMap K[X] (RatFunc K) (X ^ p + 1) := by
  have h1 : cnfNum p (-1 : K) 1 (-1) = X ^ p - 1 := by
    rw [cnfNum, one_mul, map_neg, map_one]
    ring
  have h2 : cnfDen p (-1 : K) = X ^ p + 1 := by
    rw [cnfDen, map_neg, map_one]
    ring
  rw [cnf, h1, h2]

/-! ## The channel map is the symmetric form in the conjugated coordinate -/

omit [CharZero K] in
theorem aeval_treeConj_weight {u v : K} (huv : u ≠ v) (a : K) :
    Polynomial.aeval (treeConj u v) (1 + C a * X : K[X])
      = algebraMap K[X] (RatFunc K) (C u - C v * X + C a * (X - 1))
        / algebraMap K[X] (RatFunc K) (C u - C v * X) := by
  have hd0 : algebraMap K[X] (RatFunc K) (C u - C v * X) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (treeConjDen_ne_zero huv)
  have hCa : (algebraMap K (RatFunc K) a : RatFunc K)
      = algebraMap K[X] (RatFunc K) (C a) := by
    rw [RatFunc.algebraMap_C]; rfl
  rw [map_add, map_mul, Polynomial.aeval_one, Polynomial.aeval_X, Polynomial.aeval_C, treeConj,
    hCa, map_add, map_mul, eq_div_iff hd0, add_mul, one_mul, mul_assoc,
    div_mul_cancel₀ _ hd0]

omit [CharZero K] in
theorem aeval_treeConj_weight_u {u v : K} (huv : u ≠ v) :
    Polynomial.aeval (treeConj u v) (1 + C u * X : K[X])
      = RatFunc.C (u - v) * RatFunc.X
        / algebraMap K[X] (RatFunc K) (C u - C v * X) := by
  rw [aeval_treeConj_weight huv]
  congr 1
  rw [show (C u - C v * X + C u * (X - 1) : K[X]) = C (u - v) * X by
    rw [map_sub]; ring, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]

omit [CharZero K] in
theorem aeval_treeConj_weight_v {u v : K} (huv : u ≠ v) :
    Polynomial.aeval (treeConj u v) (1 + C v * X : K[X])
      = RatFunc.C (u - v) / algebraMap K[X] (RatFunc K) (C u - C v * X) := by
  rw [aeval_treeConj_weight huv]
  congr 1
  rw [show (C u - C v * X + C v * (X - 1) : K[X]) = C (u - v) by
    rw [map_sub]; ring, RatFunc.algebraMap_C]

omit [CharZero K] in
/-- **The channel map becomes the symmetric form.** -/
theorem subst_treeConj_treeRG {p : ℕ} (hp : 0 < p) {u v : K} (huv : u ≠ v)
    (hPhi : ¬ ∃ c : K, treeConj u v = RatFunc.C c) :
    ratFuncSubstitutionAlgHom (treeConj u v) hPhi (treeRG p u v)
      = algebraMap K[X] (RatFunc K) (X ^ p - 1)
        / algebraMap K[X] (RatFunc K) (X ^ p + 1) := by
  have hd0 : algebraMap K[X] (RatFunc K) (C u - C v * X) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (treeConjDen_ne_zero huv)
  have hwne : u - v ≠ 0 := sub_ne_zero.mpr huv
  have huv0 : (RatFunc.C (u - v) : RatFunc K) ≠ 0 := by
    set w := u - v with hw
    simpa using hwne
  have hXp1 : (algebraMap K[X] (RatFunc K) (X ^ p + 1) : RatFunc K) ≠ 0 := by
    refine algebraMap_ne_zero_of_ne_zero ?_
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp [zero_pow (by omega : p ≠ 0)] at this
  have hXR : (algebraMap K[X] (RatFunc K) (X ^ p + 1) : RatFunc K) = RatFunc.X ^ p + 1 := by
    rw [map_add, map_pow, RatFunc.algebraMap_X, map_one]
  have hXR' : (algebraMap K[X] (RatFunc K) (X ^ p - 1) : RatFunc K) = RatFunc.X ^ p - 1 := by
    rw [map_sub, map_pow, RatFunc.algebraMap_X, map_one]
  have hnum : Polynomial.aeval (treeConj u v) (treeNum p u v)
      = RatFunc.C (u - v) ^ p * (RatFunc.X ^ p - 1)
        / (algebraMap K[X] (RatFunc K) (C u - C v * X)) ^ p := by
    rw [treeNum, map_sub, map_pow, map_pow, aeval_treeConj_weight_u huv,
      aeval_treeConj_weight_v huv, div_pow, div_pow, mul_pow, ← sub_div]
    congr 1
    ring
  have hden : Polynomial.aeval (treeConj u v) (treeDen p u v)
      = RatFunc.C (u - v) ^ p * (RatFunc.X ^ p + 1)
        / (algebraMap K[X] (RatFunc K) (C u - C v * X)) ^ p := by
    rw [treeDen, map_add, map_pow, map_pow, aeval_treeConj_weight_u huv,
      aeval_treeConj_weight_v huv, div_pow, div_pow, mul_pow, ← add_div]
    congr 1
    ring
  have hden0 : Polynomial.aeval (treeConj u v) (treeDen p u v) ≠ 0 := by
    rw [hden]
    refine div_ne_zero (mul_ne_zero (pow_ne_zero _ huv0) ?_) (pow_ne_zero _ hd0)
    rw [← hXR]
    exact hXp1
  have hXp1' : (RatFunc.X ^ p + 1 : RatFunc K) ≠ 0 := by rw [← hXR]; exact hXp1
  rw [treeRG, map_div₀, ratFuncSubstitutionAlgHom_aeval, ratFuncSubstitutionAlgHom_aeval,
    hnum, hden, hXR, hXR']
  field_simp

/-! ## The normal form in the conjugated coordinate -/

omit [CharZero K] in
theorem cnfNum_sub_cnfDen (p : ℕ) {u v : K} (hv1 : v ≠ 1) (hv2 : v ≠ -1) :
    cnfNum p (treeA u v) (treeB u v) (treeLam v) - cnfDen p (treeLam v)
      = C ((u - v) / (1 - v)) * (X ^ p - 1) := by
  have hv1' : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have hv2' : (1 : K) + v ≠ 0 := by
    intro h
    exact hv2 (by linear_combination h)
  have hvm : v - 1 ≠ 0 := sub_ne_zero.mpr hv1
  have hA : treeA u v = -((u - v) / (1 - v)) + 1 := by
    rw [treeA]; field_simp; ring
  have hBlam : treeB u v * treeLam v = treeLam v - (u - v) / (1 - v) := by
    rw [treeB, treeLam]; field_simp; ring
  rw [cnfNum, cnfDen, hA, hBlam, map_add, map_neg, map_one, map_sub]
  ring

omit [CharZero K] in
theorem C_mul_cnfDen_sub (p : ℕ) {u v : K} (hv1 : v ≠ 1) (hv2 : v ≠ -1) :
    C u * cnfDen p (treeLam v) - C v * cnfNum p (treeA u v) (treeB u v) (treeLam v)
      = C ((u - v) / (1 - v)) * (X ^ p + 1) := by
  have hv1' : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have hv2' : (1 : K) + v ≠ 0 := by
    intro h
    exact hv2 (by linear_combination h)
  have hvm : v - 1 ≠ 0 := sub_ne_zero.mpr hv1
  have h1 : u - v * treeA u v = (u - v) / (1 - v) := by
    rw [treeA]; field_simp; ring
  have h2 : v * (treeB u v * treeLam v) - u * treeLam v = (u - v) / (1 - v) := by
    rw [treeB, treeLam]; field_simp; ring
  have e1 : (C u - C v * C (treeA u v) : K[X]) = C ((u - v) / (1 - v)) := by
    rw [← map_mul, ← map_sub, h1]
  have e2 : (C v * C (treeB u v * treeLam v) - C u * C (treeLam v) : K[X])
      = C ((u - v) / (1 - v)) := by
    rw [← map_mul, ← map_mul, ← map_sub, h2]
  rw [cnfNum, cnfDen]
  linear_combination e1 + (X : K[X]) ^ p * e2

omit [CharZero K] in
/-- **The normal form becomes the symmetric form in the conjugated coordinate.** -/
theorem subst_cnf_treeConj {p : ℕ} (hp : 0 < p) {u v : K} (huv : u ≠ v) (hv1 : v ≠ 1)
    (hv2 : v ≠ -1)
    (hcnf : ¬ ∃ c : K, cnf p (treeA u v) (treeB u v) (treeLam v) = RatFunc.C c) :
    ratFuncSubstitutionAlgHom (cnf p (treeA u v) (treeB u v) (treeLam v)) hcnf (treeConj u v)
      = algebraMap K[X] (RatFunc K) (X ^ p - 1)
        / algebraMap K[X] (RatFunc K) (X ^ p + 1) := by
  have hv1' : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have hlam : treeLam v ≠ 0 := by
    rw [treeLam]
    refine div_ne_zero ?_ (sub_ne_zero.mpr hv1)
    intro h
    exact hv2 (by linear_combination h)
  have hkap : (u - v) / (1 - v) ≠ 0 := div_ne_zero (sub_ne_zero.mpr huv) hv1'
  set N : K[X] := cnfNum p (treeA u v) (treeB u v) (treeLam v) with hN
  set D : K[X] := cnfDen p (treeLam v) with hD
  have hD0 : algebraMap K[X] (RatFunc K) D ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero (cnfDen_ne_zero hp _)
  have hCk : (C ((u - v) / (1 - v)) : K[X]) ≠ 0 := by
    rwa [ne_eq, Polynomial.C_eq_zero]
  have hCkR : algebraMap K[X] (RatFunc K) (C ((u - v) / (1 - v))) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero hCk
  have hXp1 : (X ^ p + 1 : K[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp [zero_pow (by omega : p ≠ 0)] at this
  have hXp1R : algebraMap K[X] (RatFunc K) (X ^ p + 1) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero hXp1
  have hsub : (C u * D - C v * N : K[X]) ≠ 0 := by
    rw [C_mul_cnfDen_sub p hv1 hv2]
    exact mul_ne_zero hCk hXp1
  have hsubR : algebraMap K[X] (RatFunc K) (C u * D - C v * N) ≠ 0 :=
    algebraMap_ne_zero_of_ne_zero hsub
  have e1 : cnf p (treeA u v) (treeB u v) (treeLam v) - 1
      = algebraMap K[X] (RatFunc K) (N - D) / algebraMap K[X] (RatFunc K) D := by
    rw [cnf, ← hN, ← hD, map_sub, eq_div_iff hD0, sub_mul, div_mul_cancel₀ _ hD0, one_mul]
  have e2 : (RatFunc.C u : RatFunc K) - RatFunc.C v * cnf p (treeA u v) (treeB u v) (treeLam v)
      = algebraMap K[X] (RatFunc K) (C u * D - C v * N)
        / algebraMap K[X] (RatFunc K) D := by
    rw [cnf, ← hN, ← hD, map_sub, map_mul, map_mul, ← RatFunc.algebraMap_C,
      ← RatFunc.algebraMap_C, eq_div_iff hD0, sub_mul, mul_assoc, div_mul_cancel₀ _ hD0]
  have hval : Polynomial.aeval (cnf p (treeA u v) (treeB u v) (treeLam v)) (C u - C v * X : K[X])
      = (RatFunc.C u : RatFunc K)
        - RatFunc.C v * cnf p (treeA u v) (treeB u v) (treeLam v) := by
    rw [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C]
    rfl
  have hval1 : Polynomial.aeval (cnf p (treeA u v) (treeB u v) (treeLam v)) (X - 1 : K[X])
      = cnf p (treeA u v) (treeB u v) (treeLam v) - 1 := by
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_one]
  rw [treeConj, map_div₀, ratFuncSubstitutionAlgHom_aeval, ratFuncSubstitutionAlgHom_aeval,
    hval, hval1, e1, e2, cnfNum_sub_cnfDen p hv1 hv2,
    C_mul_cnfDen_sub p hv1 hv2, map_mul, map_mul]
  field_simp

/-! ## No Ritt cocycle for the channel map -/

omit [CharZero K] in
theorem treeConj_not_isConst {u v : K} (huv : u ≠ v) :
    ¬ ∃ c : K, treeConj u v = RatFunc.C c := by
  rintro ⟨c, hc⟩
  have hX1 : (X - 1 : K[X]) ≠ 0 := by
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp at this
  have hm1 : rootMultiplicity (1 : K) (X - 1 : K[X]) = 1 := by
    rw [show (X - 1 : K[X]) = X - C 1 by rw [map_one]]
    exact Polynomial.rootMultiplicity_X_sub_C_self
  have hm2 : rootMultiplicity (1 : K) (C u - C v * X : K[X]) = 0 := by
    refine Polynomial.rootMultiplicity_eq_zero ?_
    simp only [Polynomial.IsRoot, eval_sub, eval_mul, eval_C, eval_X, mul_one]
    exact sub_ne_zero.mpr huv
  have hord := ratOrder_algebraMap_div hX1 (treeConjDen_ne_zero huv) (1 : K)
  rw [← treeConj, hc, ratOrder_C, hm1, hm2] at hord
  omega

theorem ratFuncDeriv_treeConj_ne_zero {u v : K} (huv : u ≠ v) :
    ratFuncDeriv (treeConj u v) ≠ 0 := by
  have hnum : derivative (X - 1 : K[X]) * (C u - C v * X) - (X - 1) * derivative (C u - C v * X)
      = C (u - v) := by
    rw [derivative_sub, derivative_X, derivative_one, derivative_sub, derivative_C,
      derivative_C_mul, derivative_X, map_sub]
    ring
  rw [treeConj, ratFuncDeriv_div (treeConjDen_ne_zero huv), hnum]
  refine div_ne_zero (algebraMap_ne_zero_of_ne_zero ?_)
    (algebraMap_ne_zero_of_ne_zero (pow_ne_zero _ (treeConjDen_ne_zero huv)))
  rwa [ne_eq, Polynomial.C_eq_zero, sub_eq_zero]

/-- **The tree channel map preserves no rational `k`-differential up to scale.** -/
theorem treeRG_no_cocycle [IsAlgClosed K] {p : ℕ} (hp : 2 ≤ p) {u v : K}
    (huv : u ≠ v) (hu1 : u ≠ 1) (hu2 : u ≠ -1) (hv1 : v ≠ 1) (hv2 : v ≠ -1)
    (hpow : treeA u v ^ p ≠ treeB u v ^ p)
    (hApole : 1 - treeLam v * treeA u v ^ p ≠ 0)
    (htwo : p = 2 →
      (treeA u v - treeB u v * treeLam v * treeA u v ^ p)
          / (1 - treeLam v * treeA u v ^ p) ≠ -treeA u v
        ∧ (treeA u v - treeB u v * treeLam v * treeA u v ^ p)
          / (1 - treeLam v * treeA u v ^ p) ≠ -treeB u v)
    {hR : ¬ ∃ c : K, treeRG p u v = RatFunc.C c}
    {k : ℤ} (hk : k ≠ 0) {b : K} (hb : b ≠ 0) {G : RatFunc K} (hG : G ≠ 0)
    (heq : IsRatAffineTransport (treeRG p u v) hR k (RatFunc.C b) 0 G) : False := by
  have hp0 : 0 < p := by omega
  have hv1' : (1 : K) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
  have hv2' : (1 : K) + v ≠ 0 := fun h => hv2 (by linear_combination h)
  have hA0 : treeA u v ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hu1)) hv1'
  have hB0 : treeB u v ≠ 0 := by
    refine div_ne_zero ?_ hv2'
    intro h
    exact hu2 (by linear_combination h)
  have hlam : treeLam v ≠ 0 := div_ne_zero hv2' (sub_ne_zero.mpr hv1)
  have hAB : treeA u v ≠ treeB u v := by
    intro h
    apply hpow
    rw [h]
  have hcnf : ¬ ∃ c : K, cnf p (treeA u v) (treeB u v) (treeLam v) = RatFunc.C c :=
    cnf_not_isConst hp0 hlam hAB
  have hPhi : ¬ ∃ c : K, treeConj u v = RatFunc.C c := treeConj_not_isConst huv
  have hsym : ratFuncSubstitutionAlgHom (treeConj u v) hPhi (treeRG p u v)
      = cnf p (-1 : K) 1 (-1) := by
    rw [subst_treeConj_treeRG hp0 huv hPhi, cnf_symmetric]
  have hcomp : ¬ ∃ c : K, ratFuncSubstitutionAlgHom (treeConj u v) hPhi (treeRG p u v)
      = RatFunc.C c := by
    rw [hsym]
    exact cnf_not_isConst hp0 (by norm_num) (by norm_num)
  have hsemi : ratFuncSubstitutionAlgHom (cnf p (treeA u v) (treeB u v) (treeLam v)) hcnf
        (treeConj u v)
      = ratFuncSubstitutionAlgHom (treeConj u v) hPhi (treeRG p u v) := by
    rw [subst_cnf_treeConj hp0 huv hv1 hv2 hcnf, subst_treeConj_treeRG hp0 huv hPhi]
  have htrans := isRatAffineTransport_of_semiconj hcnf hR hPhi hcomp hsemi heq
  exact cnf_no_cocycle_general hp hlam hA0 hB0 hAB hpow hApole htwo hk hb
    (transport_ne_zero hPhi (ratFuncDeriv_treeConj_ne_zero huv) hG) htrans

end

end GaloisForLFunctions.HTGeometry
