import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheTrickleDownInequalityIsTheSquareRootCount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheFrobeniusSpanDefectCountsTheOuterEigenvalues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteConfigurationPontryaginLaw
import GaloisForLFunctions.RHTower.WeilKloostermanBound

/-!
# The local factor trickles down by Ramanujan

A curve datum of genus `g` has `2g` normalized eigenvalues; a genus-one datum is a local factor
`1 − aT + qT²`, `β + β′ = a/√q`. A finite piece of the Frobenius ladder decides the Lorentzian
structure at every depth.

* **Finite depth decides** (`unitary_of_isHyperbolic_frobeniusGram`,
  `forall_weightedTrickleDown_of_isHyperbolic`): if the ladder `H, V, Γ_0, …, Γ_{2g−1}` has the
  Hodge index, the datum is unitary, so `(TD_π)` holds on every ladder. The span defect on real
  classes is the Toeplitz form of the power sums, nonnegative on complex classes as well, and a
  nonnegative Toeplitz form of size `2g` forces `|β_i| = 1` (Pontryagin law of
  ArithmeticCastelnuovoSeveri).
* **Depth one is the Ramanujan bound** (`frobeniusGram_one_isHyperbolic_iff`): the Gram of
  `H, V, Γ_0, Γ_1` has one positive square iff `|a| ≤ 2√q`. The span defect is the Toeplitz form
  `[[2, t], [t, 2]]`, `t = a/√q`.
* **Depth one decides genus one** (`unitary_of_abs_trace_one_le`,
  `forall_weightedTrickleDown_of_abs_trace_one_le`): `|t| ≤ 2` forces `|β| = 1`, so the Hodge index
  on the first ladder gives it, and `(TD_π)`, on every ladder. Depth zero never decides: every
  genus-one datum passes it, the golden fake included (`golden_depth_one_sharp`).
* **The Ramanujan datum** (`ramanujanDatum`): every `a` with `|a| ≤ 2√q` is realized by the
  conjugate pair `t/2 ± i√(1 − t²/4)`.
* **The Kloosterman factor trickles down** (`kloosterman_isReal`,
  `kloosterman_weightedTrickleDown`, `kloosterman_hasHyperbolicLinks`): the Kloosterman sum is real,
  and by Weil's bound `|K(a)| ≤ 2√p` the local factor `1 + K(a)T + pT²` is the Ramanujan datum of
  `−K(a)`: every Frobenius ladder of it is Metzler, satisfies `(TD_π)` and has hyperbolic links.

So the local Lorentzian input at a prime is exactly the Riemann hypothesis over `𝔽_p` for the local
factor, a local statement. Together with the Euler-product closure — Lorentzian for every
nonnegative local datum and not the Weil pairing (`LocalFactorsAndTheEulerProductClosure`) — this
places the whole content of the Hodge index over `ℤ` in the local-to-global step.
-/

noncomputable section

open Matrix Finset Complex

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open ArithmeticCastelnuovoSeveri HTGeometry

variable {ι : Type*} [Fintype ι]

/-! ### Finite depth decides -/

/-- On a real matrix the Hermitian form splits into the forms of the real and imaginary parts. -/
theorem hermQuad_spanGram_eq (D : CurveDatum ι) (n : ℕ) (z : Fin n → ℂ) :
    hermQuad (D.spanGram n) z =
      hermQuad (D.spanGram n) (fun k => ((z k).re : ℂ)) +
        hermQuad (D.spanGram n) (fun k => ((z k).im : ℂ)) := by
  have key : ∀ w : Fin n → ℂ, hermQuad (D.spanGram n) w = ∑ k : Fin n, ∑ l : Fin n,
      D.trace (Nat.dist k l) * ((w k).re * (w l).re + (w k).im * (w l).im) := fun w => by
    simp only [hermQuad, dotProduct, mulVec, CurveDatum.spanGram, Pi.star_apply, Finset.mul_sum,
      Complex.re_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
    ring
  rw [key, key, key, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Finite depth decides.** If the Frobenius ladder of depth `|ι| − 1` (the graphs
`Γ_0, …, Γ_{2g−1}`) has the Hodge index, the datum is unitary. -/
theorem unitary_of_isHyperbolic_frobeniusGram (D : CurveDatum ι)
    (h : IsHyperbolic (frobeniusGram D (Fintype.card ι - 1))) : ∀ i, ‖D.β i‖ = 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · intro i; exact absurd (Fintype.card_pos_iff.mpr ⟨i⟩) (by omega)
  have hn : Fintype.card ι - 1 + 1 = Fintype.card ι := by omega
  have hdef := (frobeniusGram_isHyperbolic_iff D _).mp h
  rw [hn] at hdef
  -- the Toeplitz form is nonnegative on real classes
  have htoep : ∀ e : ℕ → ℝ, 0 ≤ D.toeplitz (range (Fintype.card ι)) e := fun e => by
    have := hdef (fun k => e k / D.sqrtq ^ k)
    rw [CurveDatum.spanDefect_eq_toeplitz] at this
    convert this using 2
    funext k
    rw [div_mul_cancel₀ _ (pow_ne_zero _ D.sqrtq_pos.ne')]
  -- hence on complex classes, so the Gram has no negative square
  have hreal : ∀ x : Fin (Fintype.card ι) → ℝ,
      0 ≤ hermQuad (D.spanGram (Fintype.card ι)) (fun k => (x k : ℂ)) := fun x => by
    have := D.hermQuad_spanGram_ofReal (Fintype.card ι)
      (fun m => if hm : m < Fintype.card ι then x ⟨m, hm⟩ else 0)
    simp only [Fin.is_lt, dif_pos, Fin.eta] at this
    rw [this]
    exact htoep _
  apply (D.unitary_iff_negIndex_spanGram_eq_zero).mpr
  refine negIndex_eq_zero_of_hermQuad_nonneg fun z => ?_
  rw [hermQuad_spanGram_eq]
  exact add_nonneg (hreal fun k => (z k).re) (hreal fun k => (z k).im)

/-- **Depth `2g − 1` gives every depth.** A datum with nonnegative counts whose ladder of depth
`|ι| − 1` has the Hodge index satisfies `(TD_π)` on every Frobenius ladder. -/
theorem forall_weightedTrickleDown_of_isHyperbolic (D : CurveDatum ι)
    (hN : ∀ j, 1 ≤ j → 0 ≤ D.pointCount j)
    (h : IsHyperbolic (frobeniusGram D (Fintype.card ι - 1))) :
    ∀ K, WeightedTrickleDown (frobeniusWeight D K) (frobeniusGram D K) :=
  (forall_weightedTrickleDown_iff_unitary D hN).mpr (unitary_of_isHyperbolic_frobeniusGram D h)

/-! ### Depth one is the Ramanujan bound -/

/-- **Depth one is the Ramanujan bound.** For a genus-one datum the Gram of `H, V, Γ_0, Γ_1` has
one positive square iff `|trace 1| ≤ 2`, i.e. `|a| ≤ 2√q`. -/
theorem frobeniusGram_one_isHyperbolic_iff (D : CurveDatum (Fin 2)) :
    IsHyperbolic (frobeniusGram D 1) ↔ |D.trace 1| ≤ 2 := by
  have htoep : ∀ e : ℕ → ℝ, D.toeplitz (range 2) e =
      2 * e 0 ^ 2 + 2 * D.trace 1 * (e 0 * e 1) + 2 * e 1 ^ 2 := fun e => by
    rw [CurveDatum.toeplitz]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have d01 : Nat.dist 0 1 = 1 := rfl
    have d10 : Nat.dist 1 0 = 1 := rfl
    rw [Nat.dist_self, Nat.dist_self, d01, d10, D.trace_zero, Fintype.card_fin]
    push_cast; ring
  rw [frobeniusGram_isHyperbolic_iff]
  simp_rw [CurveDatum.spanDefect_eq_toeplitz, htoep]
  set t := D.trace 1
  have hs := D.sqrtq_pos
  constructor
  · intro h
    rcases le_total 0 t with ht | ht
    · have := h (fun k => if k = 0 then 1 else -1 / D.sqrtq)
      simp only [if_pos, one_ne_zero, if_false, pow_zero, mul_one, pow_one] at this
      rw [div_mul_cancel₀ _ hs.ne'] at this
      rw [abs_of_nonneg ht]; nlinarith
    · have := h (fun k => if k = 0 then 1 else 1 / D.sqrtq)
      simp only [if_pos, one_ne_zero, if_false, pow_zero, mul_one, pow_one] at this
      rw [div_mul_cancel₀ _ hs.ne'] at this
      rw [abs_of_nonpos ht]; nlinarith
  · intro h d
    have h1 := abs_le.mp h
    nlinarith [sq_nonneg (d 0 * D.sqrtq ^ 0 + d 1 * D.sqrtq ^ 1),
      sq_nonneg (d 0 * D.sqrtq ^ 0 - d 1 * D.sqrtq ^ 1)]

/-- **Depth one decides genus one.** A genus-one datum with `|trace 1| ≤ 2` is unitary. -/
theorem unitary_of_abs_trace_one_le (D : CurveDatum (Fin 2)) (h : |D.trace 1| ≤ 2) :
    ∀ i, ‖D.β i‖ = 1 :=
  unitary_of_isHyperbolic_frobeniusGram D ((frobeniusGram_one_isHyperbolic_iff D).mpr h)

/-- **Depth one gives every depth.** A genus-one datum with nonnegative counts whose first ladder
has the Hodge index satisfies `(TD_π)` on every Frobenius ladder. -/
theorem forall_weightedTrickleDown_of_abs_trace_one_le (D : CurveDatum (Fin 2))
    (hN : ∀ j, 1 ≤ j → 0 ≤ D.pointCount j) (h : IsHyperbolic (frobeniusGram D 1)) :
    ∀ K, WeightedTrickleDown (frobeniusWeight D K) (frobeniusGram D K) :=
  (forall_weightedTrickleDown_iff_unitary D hN).mpr
    (unitary_of_abs_trace_one_le D ((frobeniusGram_one_isHyperbolic_iff D).mp h))

/-- **Depth one is sharp for genus one.** Every genus-one datum has the Hodge index on the
ladder `H, V, Γ_0`, while the golden fake, non-unitary, fails it on `H, V, Γ_0, Γ_1`. -/
theorem isHyperbolic_frobeniusGram_zero (D : CurveDatum (Fin 2)) :
    IsHyperbolic (frobeniusGram D 0) := by
  rw [frobeniusGram_isHyperbolic_iff]
  intro d
  rw [CurveDatum.spanDefect_eq_toeplitz, CurveDatum.toeplitz]
  simp only [zero_add, Finset.sum_range_one, Nat.dist_self, D.trace_zero, Fintype.card_fin]
  push_cast
  nlinarith [sq_nonneg (d 0 * D.sqrtq ^ 0)]

theorem golden_depth_one_sharp :
    IsHyperbolic (frobeniusGram goldenDatum 0) ∧ ¬ IsHyperbolic (frobeniusGram goldenDatum 1) ∧
      ¬ ∀ i, ‖goldenDatum.β i‖ = 1 :=
  ⟨isHyperbolic_frobeniusGram_zero _, golden_not_isHyperbolic, goldenDatum_not_unitary⟩

/-! ### The Ramanujan datum -/

/-- The normalized eigenvalue `t/2 + i√(1 − t²/4)`, `t = a/√q`. -/
def ramanujanEigen (q a : ℝ) : ℂ :=
  ⟨a / Real.sqrt q / 2, Real.sqrt (1 - (a / Real.sqrt q / 2) ^ 2)⟩

theorem normSq_ramanujanEigen {q a : ℝ} (hq : 0 < q) (ha : |a| ≤ 2 * Real.sqrt q) :
    Complex.normSq (ramanujanEigen q a) = 1 := by
  have hs := Real.sqrt_pos.mpr hq
  have ht : (a / Real.sqrt q / 2) ^ 2 ≤ 1 := by
    rw [div_div, div_pow, div_le_one (by positivity)]
    have := sq_abs a ▸ pow_le_pow_left₀ (abs_nonneg a) ha 2
    nlinarith
  rw [Complex.normSq_apply]
  simp only [ramanujanEigen]
  rw [← sq, ← sq, Real.sq_sqrt (by linarith)]
  ring

/-- **The Ramanujan datum** of the local factor `1 − aT + qT²`, `|a| ≤ 2√q`: the conjugate pair
`t/2 ± i√(1 − t²/4)`, exchanged by conjugation and by the functional equation. -/
def ramanujanDatum (q : ℝ) (hq : 1 < q) (a : ℝ) (ha : |a| ≤ 2 * Real.sqrt q) :
    CurveDatum (Fin 2) where
  q := q
  one_lt_q := hq
  β := ![ramanujanEigen q a, starRingEnd ℂ (ramanujanEigen q a)]
  conjPerm := Equiv.swap 0 1
  β_conjPerm i := by fin_cases i <;> simp
  fePerm := Equiv.swap 0 1
  β_fePerm i := by
    have h := normSq_ramanujanEigen (by linarith : (0 : ℝ) < q) ha
    have e : starRingEnd ℂ (ramanujanEigen q a) * ramanujanEigen q a = 1 := by
      rw [mul_comm, Complex.mul_conj, h]; simp
    fin_cases i
    · simpa using e
    · simpa [mul_comm] using e

theorem ramanujanDatum_unitary {q : ℝ} (hq : 1 < q) {a : ℝ} (ha : |a| ≤ 2 * Real.sqrt q) :
    ∀ i, ‖(ramanujanDatum q hq a ha).β i‖ = 1 := by
  have h := normSq_ramanujanEigen (by linarith : (0 : ℝ) < q) ha
  have hn : ‖ramanujanEigen q a‖ = 1 := by
    have e := Complex.normSq_eq_norm_sq (ramanujanEigen q a)
    rw [h] at e
    nlinarith [norm_nonneg (ramanujanEigen q a)]
  intro i; fin_cases i
  · simpa [ramanujanDatum] using hn
  · simpa [ramanujanDatum] using hn

theorem ramanujanDatum_trace_one {q : ℝ} (hq : 1 < q) {a : ℝ} (ha : |a| ≤ 2 * Real.sqrt q) :
    (ramanujanDatum q hq a ha).trace 1 = a / Real.sqrt q := by
  simp [CurveDatum.trace, CurveDatum.powerSum, ramanujanDatum, Fin.sum_univ_two, ramanujanEigen]

/-- Unitary data have nonnegative counts: `N_j ≥ (q^{j/2} − 1)²` for genus one. -/
theorem pointCount_nonneg_of_unitary_two (D : CurveDatum (Fin 2)) (hU : ∀ i, ‖D.β i‖ = 1)
    (j : ℕ) : 0 ≤ D.pointCount j := by
  have h := D.abs_trace_le_card_of_unitary hU j
  rw [Fintype.card_fin] at h
  push_cast at h
  have hs := D.sqrtq_pos
  have hq : D.q ^ j = (D.sqrtq ^ j) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul, D.sqrtq_sq]
  unfold CurveDatum.pointCount
  rw [hq]
  have := (abs_le.mp h).2
  nlinarith [sq_nonneg (D.sqrtq ^ j - 1), mul_le_mul_of_nonneg_left this (pow_pos hs j).le]

/-- **The Ramanujan factor trickles down**: every Frobenius ladder of the Ramanujan datum is
Metzler, satisfies `(TD_π)` and, after weighting, has hyperbolic links. -/
theorem ramanujanDatum_trickleDown {q : ℝ} (hq : 1 < q) {a : ℝ} (ha : |a| ≤ 2 * Real.sqrt q)
    (K : ℕ) :
    IsMetzler (frobeniusGram (ramanujanDatum q hq a ha) K) ∧
      WeightedTrickleDown (frobeniusWeight (ramanujanDatum q hq a ha) K)
        (frobeniusGram (ramanujanDatum q hq a ha) K) ∧
      HasHyperbolicLinks (diagConj (frobeniusWeight (ramanujanDatum q hq a ha) K)
        (frobeniusGram (ramanujanDatum q hq a ha) K)) := by
  have hU := ramanujanDatum_unitary hq ha
  have hN : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ (ramanujanDatum q hq a ha).pointCount j :=
    fun j _ _ => pointCount_nonneg_of_unitary_two _ hU j
  exact ⟨(frobeniusGram_isMetzler_iff _ K).mpr hN, weightedTrickleDown_of_unitary _ hU K hN,
    hasHyperbolicLinks_of_isHyperbolic _ K hN (frobeniusGram_isHyperbolic_of_unitary _ hU K)⟩

/-! ### The Kloosterman factor -/

section Kloosterman

open RHTower.WeilKloosterman

variable {p : ℕ} [Fact p.Prime]

/-- **The Kloosterman sum is real**: conjugation is the reindexing `x ↦ −x`. -/
theorem kloosterman_isReal (ψ : AddChar (ZMod p) ℂ) (a : ZMod p) :
    (kloosterman ψ a).im = 0 := by
  have h : starRingEnd ℂ (kloosterman ψ a) = kloosterman ψ a := by
    unfold kloosterman
    rw [map_sum]
    refine (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun x => ?_)
    simp only [Equiv.neg_apply, neg_eq_zero]
    split_ifs with hx
    · simp
    · rw [← AddChar.map_neg_eq_conj]; congr 1; field_simp; ring
  have := congrArg Complex.im h
  simp at this
  linarith

/-- **The Kloosterman factor trickles down.** For an odd prime `p`, a primitive additive character
`ψ` and `a ≠ 0`, Weil's bound makes `1 + K(a)T + pT²` a Ramanujan datum: every Frobenius ladder is
Metzler, satisfies `(TD_π)` and has hyperbolic links. -/
theorem kloosterman_trickleDown (hp2 : p ≠ 2) (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive)
    {a : ZMod p} (ha : a ≠ 0) :
    ∃ D : CurveDatum (Fin 2), D.q = p ∧ D.sqrtq * D.trace 1 = -(kloosterman ψ a).re ∧
      ∀ K, IsMetzler (frobeniusGram D K) ∧
        WeightedTrickleDown (frobeniusWeight D K) (frobeniusGram D K) ∧
        HasHyperbolicLinks (diagConj (frobeniusWeight D K) (frobeniusGram D K)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hW := kloosterman_weil_bound hp2 ψ hψ ha
  have hb : |-(kloosterman ψ a).re| ≤ 2 * Real.sqrt p := by
    rw [abs_neg]; exact (Complex.abs_re_le_norm _).trans hW
  refine ⟨ramanujanDatum p hp1 _ hb, rfl, ?_, fun K => ramanujanDatum_trickleDown hp1 hb K⟩
  rw [ramanujanDatum_trace_one hp1 hb]
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  show Real.sqrt p * (-(kloosterman ψ a).re / Real.sqrt p) = _
  field_simp

end Kloosterman

end GaloisForLFunctions.ArithmeticLorentzianGeometry
