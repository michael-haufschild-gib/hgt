import GaloisForLFunctions.HTGeometry.EulerPolePartCalculus
import GaloisForLFunctions.HTGeometry.QDifferenceLaurentOneVariable
import GaloisForLFunctions.HTGeometry.GeometricKallenLehmannHypertranscendence

/-!
# The one-loop resolvent of an ultrametric spectrum

The higher resolvent trace of the one-sided ultrametric shell spectrum satisfies a first-order
`q`-difference equation with `q = 1/p` and a two-shell rational defect

```text
Q(x) = (p−2)/(x+1)^m + 1/(x+p)^m + p^(1−m) Q(x/p).
```

Multiplying by the monomial `x^(m−1)` — an eigenvector of the dilation with eigenvalue `p^(1−m)` —
turns it into a pure additive shift, so the automorphism-family criterion applies.  The two poles
of the defect lie in one multiplicative orbit, and their weighted principal parts sum to
`(p−1)²/p ≠ 0`, so no jet combination telescopes.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- The numerator of the two-shell defect after clearing both shell denominators. -/
def resolventNum (p m : ℕ) : Polynomial k :=
  -((Polynomial.C ((p : k) - 2) * (Polynomial.X + Polynomial.C ((p : k))) ^ m
      + (Polynomial.X + 1) ^ m) * Polynomial.X ^ (m - 1))

/-- The increment of the resolvent equation in the twisted coordinate. -/
def resolventIncrement (p m : ℕ) : RatFunc k :=
  algebraMap (Polynomial k) (RatFunc k) (resolventNum p m)
    / algebraMap (Polynomial k) (RatFunc k)
      ((Polynomial.X + 1) ^ m * (Polynomial.X + Polynomial.C ((p : k))) ^ m)

theorem shellA_ne_zero [CharZero k] {p : ℕ} (hp : 1 < p) :
    ((Polynomial.X + 1 : Polynomial k)).eval (-(p : k)) ≠ 0 := by
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  intro h
  have hp1 : ((p : k)) = 1 := by linear_combination -h
  have h2 : ((p : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact hp1
  have := Nat.cast_injective (R := k) h2
  omega

theorem shellB_ne_zero [CharZero k] {p : ℕ} (hp : 1 < p) :
    ((Polynomial.X + Polynomial.C ((p : k)) : Polynomial k)).eval (-1) ≠ 0 := by
  rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  intro h
  have hp1 : ((p : k)) = 1 := by linear_combination h
  have h2 : ((p : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact hp1
  have := Nat.cast_injective (R := k) h2
  omega

theorem resolventIncrement_mul_shellA [CharZero k] {p : ℕ} (hp : 1 < p) (m : ℕ) :
    (resolventIncrement (k := k) p m)
        * (RatFunc.X - algebraMap k (RatFunc k) (-1)) ^ m
      = algebraMap (Polynomial k) (RatFunc k) (resolventNum p m)
        / algebraMap (Polynomial k) (RatFunc k) ((Polynomial.X + Polynomial.C ((p : k))) ^ m) := by
  have hlin : (RatFunc.X - algebraMap k (RatFunc k) (-1) : RatFunc k)
      = algebraMap (Polynomial k) (RatFunc k) (Polynomial.X + 1) := by
    rw [map_add, RatFunc.algebraMap_X, map_one, map_neg, map_one]
    ring
  have hA : algebraMap (Polynomial k) (RatFunc k) ((Polynomial.X + 1 : Polynomial k) ^ m) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ (fun h => by
      have := congrArg (fun P : Polynomial k => P.eval (-(p : k))) h
      simp only [Polynomial.eval_zero] at this
      exact shellA_ne_zero hp this))
  have hB : algebraMap (Polynomial k) (RatFunc k)
      ((Polynomial.X + Polynomial.C ((p : k)) : Polynomial k) ^ m) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ (fun h => by
      have := congrArg (fun P : Polynomial k => P.eval (-1)) h
      simp only [Polynomial.eval_zero] at this
      exact shellB_ne_zero hp this))
  rw [resolventIncrement, hlin, ← map_pow, map_mul]
  field_simp

theorem resolventIncrement_mul_shellB [CharZero k] {p : ℕ} (hp : 1 < p) (m : ℕ) :
    (resolventIncrement (k := k) p m)
        * (RatFunc.X - algebraMap k (RatFunc k) (-(p : k))) ^ m
      = algebraMap (Polynomial k) (RatFunc k) (resolventNum p m)
        / algebraMap (Polynomial k) (RatFunc k) ((Polynomial.X + 1) ^ m) := by
  have hlin : (RatFunc.X - algebraMap k (RatFunc k) (-(p : k)) : RatFunc k)
      = algebraMap (Polynomial k) (RatFunc k) (Polynomial.X + Polynomial.C ((p : k))) := by
    rw [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_neg]
    rw [show (RatFunc.C ((p : k)) : RatFunc k) = algebraMap k (RatFunc k) ((p : k)) from rfl]
    ring
  have hA : algebraMap (Polynomial k) (RatFunc k) ((Polynomial.X + 1 : Polynomial k) ^ m) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ (fun h => by
      have := congrArg (fun P : Polynomial k => P.eval (-(p : k))) h
      simp only [Polynomial.eval_zero] at this
      exact shellA_ne_zero hp this))
  have hB : algebraMap (Polynomial k) (RatFunc k)
      ((Polynomial.X + Polynomial.C ((p : k)) : Polynomial k) ^ m) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero _ (fun h => by
      have := congrArg (fun P : Polynomial k => P.eval (-1)) h
      simp only [Polynomial.eval_zero] at this
      exact shellB_ne_zero hp this))
  rw [resolventIncrement, hlin, ← map_pow, map_mul]
  field_simp

/-! ## The principal parts of the increment -/

theorem eval_resolventNum_A [CharZero k] (p m : ℕ) (hm : 0 < m) :
    (resolventNum (k := k) p m).eval (-1)
      = -(((p : k) - 2) * ((p : k) - 1) ^ m * (-1) ^ (m - 1)) := by
  rw [resolventNum]
  simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [show ((-1 : k) + 1) = 0 from by ring, zero_pow (by omega : m ≠ 0), add_zero]
  ring_nf

theorem eval_resolventNum_B [CharZero k] (p m : ℕ) (hm : 0 < m) :
    (resolventNum (k := k) p m).eval (-(p : k))
      = -((1 - (p : k)) ^ m * (-(p : k)) ^ (m - 1)) := by
  rw [resolventNum]
  simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
  rw [show (-(p : k) + (p : k)) = 0 from by ring, zero_pow (by omega : m ≠ 0), mul_zero, zero_add,
    show (-(p : k) + 1) = 1 - (p : k) from by ring]

theorem polePart_resolventIncrement_A [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 0 < m) :
    polePart (resolventIncrement (k := k) p m) (-1) m
      = -(((p : k) - 2) * (-1) ^ (m - 1)) := by
  have hQ : ((Polynomial.X + Polynomial.C ((p : k)) : Polynomial k) ^ m).eval (-1) ≠ 0 := by
    rw [Polynomial.eval_pow]
    exact pow_ne_zero _ (shellB_ne_zero hp)
  have h := polePart_top_of_repr (g := resolventIncrement (k := k) p m) (c := (-1 : k)) (m := m)
    (P := resolventNum p m) (Q := (Polynomial.X + Polynomial.C ((p : k))) ^ m) hQ
    (resolventIncrement_mul_shellA hp m)
  rw [h, eval_resolventNum_A p m hm, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  have hne : ((p : k) - 1) ^ m ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h1
    have hp1 : ((p : k)) = 1 := by linear_combination h1
    have h2 : ((p : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact hp1
    have := Nat.cast_injective (R := k) h2
    omega
  rw [show ((-1 : k) + (p : k)) = ((p : k) - 1) from by ring]
  field_simp

theorem polePart_resolventIncrement_B [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 0 < m) :
    polePart (resolventIncrement (k := k) p m) (-(p : k)) m
      = -((-(p : k)) ^ (m - 1)) := by
  have hQ : ((Polynomial.X + 1 : Polynomial k) ^ m).eval (-(p : k)) ≠ 0 := by
    rw [Polynomial.eval_pow]
    exact pow_ne_zero _ (shellA_ne_zero hp)
  have h := polePart_top_of_repr (g := resolventIncrement (k := k) p m) (c := (-(p : k))) (m := m)
    (P := resolventNum p m) (Q := (Polynomial.X + 1) ^ m) hQ
    (resolventIncrement_mul_shellB hp m)
  rw [h, eval_resolventNum_B p m hm, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  have hne : ((1 : k) - (p : k)) ^ m ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h1
    have hp1 : ((p : k)) = 1 := by linear_combination -h1
    have h2 : ((p : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact hp1
    have := Nat.cast_injective (R := k) h2
    omega
  rw [show ((-(p : k)) + 1) = (1 - (p : k)) from by ring]
  field_simp

theorem polePart_resolventIncrement_A_vanish [CharZero k] {p : ℕ} (hp : 1 < p) (m : ℕ) :
    ∀ e : ℕ, m < e → polePart (resolventIncrement (k := k) p m) (-1) e = 0 := by
  intro e he
  refine polePart_eq_zero_of_regularAt_mul_pow ?_ he
  rw [resolventIncrement_mul_shellA hp m]
  refine regularAt_of_repr (P := resolventNum p m)
    (Q := (Polynomial.X + Polynomial.C ((p : k))) ^ m) ?_ rfl
  rw [Polynomial.eval_pow]
  exact pow_ne_zero _ (shellB_ne_zero hp)

theorem polePart_resolventIncrement_B_vanish [CharZero k] {p : ℕ} (hp : 1 < p) (m : ℕ) :
    ∀ e : ℕ, m < e → polePart (resolventIncrement (k := k) p m) (-(p : k)) e = 0 := by
  intro e he
  refine polePart_eq_zero_of_regularAt_mul_pow ?_ he
  rw [resolventIncrement_mul_shellB hp m]
  refine regularAt_of_repr (P := resolventNum p m) (Q := (Polynomial.X + 1) ^ m) ?_ rfl
  rw [Polynomial.eval_pow]
  exact pow_ne_zero _ (shellA_ne_zero hp)

theorem regularAt_resolventIncrement [CharZero k] {p : ℕ} (m : ℕ) {c : k}
    (hA : c + 1 ≠ 0) (hB : c + (p : k) ≠ 0) :
    RegularAt (resolventIncrement (k := k) p m) c := by
  refine regularAt_of_repr (P := resolventNum p m)
    (Q := (Polynomial.X + 1) ^ m * (Polynomial.X + Polynomial.C ((p : k))) ^ m) ?_ rfl
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow]
  refine mul_ne_zero (pow_ne_zero _ ?_) (pow_ne_zero _ ?_)
  · rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact hA
  · rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    exact hB

/-! ## Jets of the increment -/

/-- The scalar picked up by the `J`-th Euler jet of a pole of order `m` at `c`. -/
def jetFactor (c : k) (m J : ℕ) : k := ∏ i ∈ Finset.range J, -(c * ((m : k) + i))

theorem jetFactor_A (m J : ℕ) : jetFactor (-1 : k) m J = ∏ i ∈ Finset.range J, ((m : k) + i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem jetFactor_B (p m J : ℕ) :
    jetFactor (-(p : k)) m J = ((p : k)) ^ J * jetFactor (-1 : k) m J := by
  induction J with
  | zero => simp [jetFactor]
  | succ J ih =>
      rw [jetFactor, jetFactor, Finset.prod_range_succ, Finset.prod_range_succ, ← jetFactor,
        ← jetFactor, ih, pow_succ]
      ring

theorem jetFactor_A_ne_zero [CharZero k] {m : ℕ} (hm : 0 < m) (J : ℕ) :
    jetFactor (-1 : k) m J ≠ 0 := by
  rw [jetFactor_A]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  intro h
  have hcast : (((m + i : ℕ)) : k) = 0 := by push_cast; linear_combination h
  have := Nat.cast_eq_zero.mp hcast
  omega

theorem polePart_jet_A [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 0 < m) (J : ℕ) :
    polePart (ratFuncEulerOp^[J] (resolventIncrement (k := k) p m)) (-1) (m + J)
      = jetFactor (-1 : k) m J * polePart (resolventIncrement (k := k) p m) (-1) m :=
  (polePart_eulerOp_iterate (polePart_resolventIncrement_A_vanish hp m) J).2

theorem polePart_jet_A_vanish [CharZero k] {p : ℕ} (hp : 1 < p) (m J : ℕ) :
    ∀ e : ℕ, m + J < e → polePart (ratFuncEulerOp^[J] (resolventIncrement (k := k) p m)) (-1) e
      = 0 :=
  (polePart_eulerOp_iterate (polePart_resolventIncrement_A_vanish hp m) J).1

theorem polePart_jet_B [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 0 < m) (J : ℕ) :
    polePart (ratFuncEulerOp^[J] (resolventIncrement (k := k) p m)) (-(p : k)) (m + J)
      = jetFactor (-(p : k)) m J * polePart (resolventIncrement (k := k) p m) (-(p : k)) m :=
  (polePart_eulerOp_iterate (polePart_resolventIncrement_B_vanish hp m) J).2

theorem polePart_jet_B_vanish [CharZero k] {p : ℕ} (hp : 1 < p) (m J : ℕ) :
    ∀ e : ℕ, m + J < e →
      polePart (ratFuncEulerOp^[J] (resolventIncrement (k := k) p m)) (-(p : k)) e = 0 :=
  (polePart_eulerOp_iterate (polePart_resolventIncrement_B_vanish hp m) J).1

theorem polePart_jet_other [CharZero k] {p : ℕ} (m J : ℕ) {c : k}
    (hA : c + 1 ≠ 0) (hB : c + (p : k) ≠ 0) :
    ∀ e : ℕ, 0 < e → polePart (ratFuncEulerOp^[J] (resolventIncrement (k := k) p m)) c e = 0 := by
  have hbase : ∀ e : ℕ, 0 < e → polePart (resolventIncrement (k := k) p m) c e = 0 := by
    intro e he
    exact polePart_eq_zero_of_regularAt (regularAt_ratFuncShift (regularAt_resolventIncrement m hA hB)) he
  exact polePart_eulerOp_iterate_regular hbase J

/-! ## No telescoper -/

theorem differentialJet_eq_eulerIterate (n : ℕ) (y : RatFunc k) :
    letI := cylinderDifferential (1 : k)
    differentialJet n y = ratFuncEulerOp^[n] y := by
  letI := cylinderDifferential (1 : k)
  rw [differentialJet_cylinder]
  congr 1
  funext z
  exact cylDeriv_one_eq_ratFuncEulerOp z

theorem natCast_ne_zero_of_one_lt [CharZero k] {p : ℕ} (hp : 1 < p) : ((p : k)) ≠ 0 := by
  have : (0 : ℕ) < p := by omega
  exact Nat.cast_ne_zero.mpr this.ne'

theorem natCast_pow_ne_one_local [CharZero k] {p : ℕ} (hp : 1 < p) {j : ℕ} (hj : 0 < j) :
    ((p : k)) ^ (j : ℕ) ≠ 1 := by
  intro h
  have hnat : ((p ^ j : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact h
  have heq := Nat.cast_injective (R := k) hnat
  have hlt : 1 < p ^ j := Nat.one_lt_pow (by omega) hp
  omega

theorem natCast_zpow_ne_one_local [CharZero k] {p : ℕ} (hp : 1 < p) {n : ℤ} (hn : n ≠ 0) :
    ((p : k)) ^ n ≠ 1 := by
  have hpk : ((p : k)) ≠ 0 := natCast_ne_zero_of_one_lt hp
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · intro h
    have h' : ((p : k)) ^ (-n) = 1 := by rw [zpow_neg, h, inv_one]
    rw [← Int.toNat_of_nonneg (show (0 : ℤ) ≤ -n by omega), zpow_natCast] at h'
    exact natCast_pow_ne_one_local hp (by omega : 0 < (-n).toNat) h'
  · intro h
    rw [← Int.toNat_of_nonneg (show (0 : ℤ) ≤ n by omega), zpow_natCast] at h
    exact natCast_pow_ne_one_local hp (by omega : 0 < n.toNat) h

theorem inv_natCast_zpow_ne_one [CharZero k] {p : ℕ} (hp : 1 < p) {n : ℤ} (hn : n ≠ 0) :
    (((p : k))⁻¹) ^ n ≠ 1 := by
  rw [inv_zpow]
  intro h
  exact natCast_zpow_ne_one_local hp hn (inv_eq_one.mp h)

set_option maxHeartbeats 2000000 in
theorem no_resolvent_telescoper [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 0 < m)
    (c : (Unit × ℕ) →₀ k) (hc : c ≠ 0) (y : RatFunc k) :
    letI := cylinderDifferential (1 : k)
    ratFuncScale ((p : k))⁻¹ (inv_ne_zero (natCast_ne_zero_of_one_lt hp)) y - y ≠
      Finsupp.linearCombination (RatFunc k)
        (fun q : Unit × ℕ => differentialJet q.2 (resolventIncrement (k := k) p m))
        (Finsupp.mapRange (algebraMap k (RatFunc k)) (map_zero _) c) := by
  classical
  letI := cylinderDifferential (1 : k)
  intro heq
  have hpk : ((p : k)) ≠ 0 := natCast_ne_zero_of_one_lt hp
  have hq : ((p : k))⁻¹ ≠ 0 := inv_ne_zero hpk
  -- the top jet index
  obtain ⟨q₀, hq₀⟩ : ∃ q : Unit × ℕ, c q ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (Finsupp.ext h)
  set J : ℕ := c.support.sup Prod.snd with hJ
  have hmemJ : ((), J) ∈ c.support := by
    obtain ⟨q, hqmem, hqeq⟩ := Finset.exists_mem_eq_sup c.support
      ⟨q₀, Finsupp.mem_support_iff.mpr hq₀⟩ (Prod.snd : Unit × ℕ → ℕ)
    have hqq : (((), J) : Unit × ℕ) = q := by
      rw [hJ, hqeq]
    simpa only [hqq] using hqmem
  have hcJ : c ((), J) ≠ 0 := Finsupp.mem_support_iff.mp hmemJ
  have hle : ∀ q ∈ c.support, q.2 ≤ J := fun q hqm => Finset.le_sup (f := Prod.snd) hqm
  -- the combination as a finite sum
  have hzs : ∀ q : Unit × ℕ,
      (0 : RatFunc k) • differentialJet q.2 (resolventIncrement (k := k) p m) = 0 :=
    fun q => zero_smul _ _
  have hRHS : Finsupp.linearCombination (RatFunc k)
      (fun q : Unit × ℕ => differentialJet q.2 (resolventIncrement (k := k) p m))
      (Finsupp.mapRange (algebraMap k (RatFunc k)) (map_zero _) c)
      = ∑ q ∈ c.support, algebraMap k (RatFunc k) (c q)
        * ratFuncEulerOp^[q.2] (resolventIncrement (k := k) p m) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index hzs, Finsupp.sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_eq_mul, differentialJet_eq_eulerIterate]
  rw [hRHS] at heq
  -- principal parts of the combination
  have hpole : ∀ (x : k) (e : ℕ),
      polePart (∑ q ∈ c.support, algebraMap k (RatFunc k) (c q)
        * ratFuncEulerOp^[q.2] (resolventIncrement (k := k) p m)) x e
        = ∑ q ∈ c.support, c q
          * polePart (ratFuncEulerOp^[q.2] (resolventIncrement (k := k) p m)) x e := by
    intro x e
    rw [polePart_sum]
    exact Finset.sum_congr rfl fun q _ => polePart_smul _ _ _ _
  refine no_dilationTelescoper_of_orbit_mass (q := ((p : k))⁻¹) (a := (-1 : k)) hq
    (by norm_num) (fun n hn => inv_natCast_zpow_ne_one hp hn) (d := m + J) (by omega) _ ?_ ?_
    ⟨y, heq.symm⟩
  · -- vanishing away from the two shells
    intro n hn0 hn1
    rw [hpole]
    refine Finset.sum_eq_zero fun q _ => ?_
    have hA : multOrbit ((p : k))⁻¹ (-1 : k) n + 1 ≠ 0 := by
      intro hcon
      have h' : (-1 : k) * (((p : k))⁻¹) ^ n + 1 = 0 := hcon
      exact inv_natCast_zpow_ne_one (k := k) hp hn0 (by linear_combination -h')
    have hB : multOrbit ((p : k))⁻¹ (-1 : k) n + (p : k) ≠ 0 := by
      intro hcon
      have h' : (-1 : k) * (((p : k))⁻¹) ^ n + (p : k) = 0 := hcon
      refine inv_natCast_zpow_ne_one (k := k) hp (show n + 1 ≠ 0 by omega) ?_
      rw [zpow_add₀ hq, zpow_one, show (((p : k))⁻¹) ^ n = (p : k) from by linear_combination -h']
      field_simp
    rw [polePart_jet_other m q.2 hA hB _ (by omega), mul_zero]
  · -- the weighted mass is nonzero
    have horb : multOrbit ((p : k))⁻¹ (-1 : k) (-1) = -(p : k) := by
      show (-1 : k) * (((p : k))⁻¹) ^ (-1 : ℤ) = -(p : k)
      rw [zpow_neg, zpow_one, inv_inv]
      ring
    rw [hpole (-1 : k) (m + J), hpole (multOrbit ((p : k))⁻¹ (-1 : k) (-1)) (m + J), horb]
    have hsumA : ∑ q ∈ c.support,
        c q * polePart (ratFuncEulerOp^[q.2] (resolventIncrement (k := k) p m)) (-1) (m + J)
        = c ((), J) * (jetFactor (-1 : k) m J
          * polePart (resolventIncrement (k := k) p m) (-1) m) := by
      rw [Finset.sum_eq_single ((), J)]
      · rw [polePart_jet_A hp hm J]
      · intro q hqm hqne
        have hlt : q.2 < J :=
          lt_of_le_of_ne (hle q hqm) (fun h => hqne (Prod.ext (Subsingleton.elim _ _) h))
        rw [polePart_jet_A_vanish hp m q.2 (m + J) (by omega), mul_zero]
      · intro h
        exact absurd hmemJ h
    have hsumB : ∑ q ∈ c.support,
        c q * polePart (ratFuncEulerOp^[q.2] (resolventIncrement (k := k) p m)) (-(p : k)) (m + J)
        = c ((), J) * (jetFactor (-(p : k)) m J
          * polePart (resolventIncrement (k := k) p m) (-(p : k)) m) := by
      rw [Finset.sum_eq_single ((), J)]
      · rw [polePart_jet_B hp hm J]
      · intro q hqm hqne
        have hlt : q.2 < J :=
          lt_of_le_of_ne (hle q hqm) (fun h => hqne (Prod.ext (Subsingleton.elim _ _) h))
        rw [polePart_jet_B_vanish hp m q.2 (m + J) (by omega), mul_zero]
      · intro h
        exact absurd hmemJ h
    rw [hsumA, hsumB, polePart_resolventIncrement_A hp hm, polePart_resolventIncrement_B hp hm,
      jetFactor_B]
    have hzp : (((p : k))⁻¹) ^ (((m + J : ℕ)) : ℤ) = (((p : k))⁻¹) ^ (m + J) := by
      rw [zpow_natCast]
    rw [hzp]
    have hfac : jetFactor (-1 : k) m J ≠ 0 := jetFactor_A_ne_zero hm J
    have hpow : ((-(p : k)) ^ (m - 1)) = (-1 : k) ^ (m - 1) * ((p : k)) ^ (m - 1) := by
      rw [← neg_one_mul, mul_pow]
    have hsign : ((-1 : k) ^ (m - 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hkey : c ((), J) * (jetFactor (-1 : k) m J * -(((p : k) - 2) * (-1 : k) ^ (m - 1)))
        + (((p : k))⁻¹) ^ (m + J)
          * (c ((), J) * (((p : k)) ^ J * jetFactor (-1 : k) m J * -((-(p : k)) ^ (m - 1))))
        = -(c ((), J) * jetFactor (-1 : k) m J * (-1 : k) ^ (m - 1)
            * ((((p : k)) - 1) ^ 2 / (p : k))) := by
      rw [hpow, inv_pow,
        show ((p : k)) ^ (m + J) = ((p : k)) ^ (m - 1) * ((p : k)) ^ J * (p : k) from by
          rw [show m + J = (m - 1) + J + 1 from by omega, pow_succ, pow_add]]
      field_simp
      ring
    rw [hkey]
    intro hzero
    have hp1 : ((p : k)) - 1 ≠ 0 := by
      intro h1
      have hp1' : ((p : k)) = 1 := by linear_combination h1
      have h2 : ((p : ℕ) : k) = ((1 : ℕ) : k) := by push_cast; exact hp1'
      have := Nat.cast_injective (R := k) h2
      omega
    have hne : c ((), J) * jetFactor (-1 : k) m J * (-1 : k) ^ (m - 1)
        * ((((p : k)) - 1) ^ 2 / (p : k)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero hcJ hfac) hsign) ?_
      exact div_ne_zero (pow_ne_zero _ hp1) hpk
    exact hne (by linear_combination -hzero)

/-! ## The germ and its hypertranscendence -/

theorem qDifferenceSolution_spec_zero (b : k) (hb : b ≠ 0) (ρ : LaurentSeries k)
    (hres : ∀ n : ℤ, n ≠ 0 → 1 - b ^ n ≠ 0) (h0 : ρ.coeff 0 = 0) :
    qDifferenceSolution 1 b ρ - innerDilation b hb (qDifferenceSolution 1 b ρ) = ρ := by
  refine HahnSeries.coeff_inj.mp (funext fun n => ?_)
  rw [HahnSeries.coeff_sub, coeff_innerDilation, coeff_qDifferenceSolution,
    coeff_qDifferenceSolution, one_mul]
  by_cases hn : n = 0
  · subst hn
    rw [zpow_zero, h0]
    simp
  · field_simp [hres n hn]

theorem eval_zero_resolventNum [CharZero k] (p : ℕ) {m : ℕ} (hm : 1 < m) :
    (resolventNum (k := k) p m).eval 0 = 0 := by
  rw [resolventNum]
  simp only [Polynomial.eval_neg, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [zero_pow (by omega : m - 1 ≠ 0), mul_zero, neg_zero]

theorem coeff_zero_resolventIncrement [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 1 < m) :
    (algebraMap (RatFunc k) (LaurentSeries k) (resolventIncrement (k := k) p m)).coeff 0 = 0 := by
  have hQ : (((Polynomial.X + 1) ^ m * (Polynomial.X + Polynomial.C ((p : k))) ^ m :
      Polynomial k)).eval 0 ≠ 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, zero_add,
      zero_add, one_pow, one_mul]
    exact pow_ne_zero _ (natCast_ne_zero_of_one_lt hp)
  rw [resolventIncrement, coeff_zero_algebraMap_div _ _ hQ, eval_zero_resolventNum p hm,
    zero_div]

/-- The germ solving the ultrametric resolvent constraint, in the twisted coordinate. -/
def resolventGerm [CharZero k] (p m : ℕ) : LaurentSeries k :=
  qDifferenceSolution 1 (((p : k))⁻¹)
    (-(algebraMap (RatFunc k) (LaurentSeries k) (resolventIncrement p m)))

theorem resolventGerm_shift [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ} (hm : 1 < m) :
    innerDilation ((p : k))⁻¹ (inv_ne_zero (natCast_ne_zero_of_one_lt hp))
        (resolventGerm p m)
      = resolventGerm (k := k) p m
        + algebraMap (RatFunc k) (LaurentSeries k) (resolventIncrement p m) := by
  have hres : ∀ n : ℤ, n ≠ 0 → 1 - (((p : k))⁻¹) ^ n ≠ 0 := by
    intro n hn hcon
    exact inv_natCast_zpow_ne_one (k := k) hp hn (by linear_combination -hcon)
  have h0 : (-(algebraMap (RatFunc k) (LaurentSeries k)
      (resolventIncrement (k := k) p m))).coeff 0 = 0 := by
    rw [HahnSeries.coeff_neg, coeff_zero_resolventIncrement hp hm, neg_zero]
  have h := qDifferenceSolution_spec_zero (((p : k))⁻¹)
    (inv_ne_zero (natCast_ne_zero_of_one_lt hp))
    (-(algebraMap (RatFunc k) (LaurentSeries k) (resolventIncrement (k := k) p m))) hres h0
  rw [resolventGerm]
  linear_combination -h

set_option maxHeartbeats 2000000 in
/-- **The one-loop resolvent germ is differentially transcendental** over `k(x)` in the twisted
coordinate. -/
theorem differentialIndependent_resolventGerm [CharZero k] {p : ℕ} (hp : 1 < p) {m : ℕ}
    (hm : 1 < m) :
    letI := cylinderDifferential (1 : k)
    letI := innerDifferential (k := k)
    DifferentialIndependent (RatFunc k) (fun _ : Unit => resolventGerm (k := k) p m) := by
  refine differentialIndependent_of_oneVariable_primitive (((p : k))⁻¹)
    (inv_ne_zero (natCast_ne_zero_of_one_lt hp))
    (fun n hn => inv_natCast_zpow_ne_one (k := k) hp hn)
    (resolventGerm p m) (resolventIncrement p m) (resolventGerm_shift hp hm) ?_
  intro c hc y
  exact no_resolvent_telescoper hp (by omega) c hc y

end

end GaloisForLFunctions.HTGeometry
