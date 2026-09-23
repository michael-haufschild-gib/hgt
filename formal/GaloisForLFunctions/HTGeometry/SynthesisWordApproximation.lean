/-
# A finite alphabet whose depth-`2K` words fill the unit sphere

Discretizing the rotation angles and the phases of the exact two-level synthesis into `m` equal
steps gives a finite alphabet of `K²m + Km` letters whose words of length `2K-1` reach every unit
vector of `ℂ^K` to within `(2K)·√K·(4π/m)`.  Each letter is a linear isometry, and the alphabet is
closed under inverses because the angle grid is.

Main results:
* `SynthLetter`, `synthAct` — the finite alphabet and its action.
* `exists_absWord`, `exists_phWord` — the two passes with their accumulated error.
* `exists_synthesis_word` — **every unit vector is reached within `η` by a word of length `2K-1`**.
-/
import GaloisForLFunctions.HTGeometry.TwoLevelStateSynthesis
import GaloisForLFunctions.HTGeometry.SingleOrbitPlateauWindow
import GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman

open Finset _root_.HTGeometry

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {K : ℕ}

/-! ## Norms along the two passes -/

theorem normSq_absState_apply (ψ : Fin K → ℂ) (p : ℕ) (r : Fin K) :
    ‖absState ψ p r‖ ^ (2 : ℕ)
      = (if (r : ℕ) < p then ‖ψ r‖ ^ (2 : ℕ) else if (r : ℕ) = p then (tailv ψ p) ^ (2 : ℕ) else 0) := by
  rw [absState]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · rw [norm_zero]
    ring

theorem sum_normSq_absState_zero (ψ : Fin K → ℂ) (hK : 0 < K) :
    ∑ r, ‖absState ψ 0 r‖ ^ (2 : ℕ) = ∑ r, ‖ψ r‖ ^ (2 : ℕ) := by
  classical
  rw [Finset.sum_congr rfl (fun r _ => normSq_absState_apply ψ 0 r)]
  rw [Finset.sum_eq_single (⟨0, hK⟩ : Fin K)]
  · rw [if_neg (by omega : ¬ ((⟨0, hK⟩ : Fin K) : ℕ) < 0), if_pos rfl, sq_tailv, tailSq]
    exact Finset.sum_congr rfl fun r _ => by rw [if_pos (Nat.zero_le _)]
  · intro r _ hr
    have hrne : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
    rw [if_neg (by omega), if_neg hrne]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_normSq_absState (ψ : Fin K → ℂ) (hK : 0 < K) :
    ∀ p : ℕ, p + 1 ≤ K → ∑ r, ‖absState ψ p r‖ ^ (2 : ℕ) = ∑ r, ‖ψ r‖ ^ (2 : ℕ)
  | 0, _ => sum_normSq_absState_zero ψ hK
  | (p + 1), hp => by
      have hplt : p + 1 < K := by omega
      have hpk : p < K := by omega
      obtain ⟨i, hidef⟩ : ∃ i : Fin K, i = (⟨p, hpk⟩ : Fin K) := ⟨_, rfl⟩
      obtain ⟨j, hjdef⟩ : ∃ j : Fin K, j = (⟨p + 1, hplt⟩ : Fin K) := ⟨_, rfl⟩
      have hival : (i : ℕ) = p := by rw [hidef]
      have hjval : (j : ℕ) = p + 1 := by rw [hjdef]
      have hij : i ≠ j := by
        intro h
        rw [h, hjval] at hival
        omega
      have hstep := rotStep ψ (i := i) (j := j) (by rw [hival, hjval])
      rw [hival] at hstep
      rw [← hstep, sum_normSq_rotAct hij]
      exact sum_normSq_absState ψ hK p (by omega)

theorem sum_normSq_phState (ψ : Fin K → ℂ) (q : ℕ) :
    ∑ r, ‖phState ψ q r‖ ^ (2 : ℕ) = ∑ r, ‖ψ r‖ ^ (2 : ℕ) := by
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [phState]
  split_ifs
  · rfl
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_norm]

/-! ## The finite alphabet -/

/-- A letter: a two-level rotation at a grid angle, or a coordinate phase at a grid angle. -/
abbrev SynthLetter (K m : ℕ) : Type := (Fin K × Fin K × Fin m) ⊕ (Fin K × Fin m)

/-- The gate of one letter, on coordinate functions. -/
def synthGate (K m : ℕ) : SynthLetter K m → (Fin K → ℂ) → (Fin K → ℂ)
  | Sum.inl g => if g.1 = g.2.1 then id else rotAct g.1 g.2.1 (gridAngle m g.2.2)
  | Sum.inr g => phaseAct g.1 (gridAngle m g.2)

/-- The action of one letter on register states. -/
def synthAct (K m : ℕ) :
    SynthLetter K m → EuclideanSpace ℂ (Fin K) → EuclideanSpace ℂ (Fin K) :=
  fun g x => eucVec (synthGate K m g (WithLp.ofLp x))

theorem dist_le_of_pointwise {u v : Fin K → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ r, ‖u r - v r‖ ≤ c) :
    dist (eucVec u) (eucVec v) ≤ Real.sqrt (K : ℝ) * c := by
  rw [dist_eucVec]
  have hsum : ∑ r, ‖u r - v r‖ ^ (2 : ℕ) ≤ (K : ℝ) * c ^ (2 : ℕ) := by
    refine le_trans (Finset.sum_le_sum fun r _ => pow_le_pow_left₀ (norm_nonneg _) (h r) 2)
      (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine le_trans (Real.sqrt_le_sqrt hsum) (le_of_eq ?_)
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hc]

theorem dist_eucVec_ofLp (x y : EuclideanSpace ℂ (Fin K)) :
    dist x y = Real.sqrt (∑ i, ‖WithLp.ofLp x i - WithLp.ofLp y i‖ ^ (2 : ℕ)) :=
  dist_eucVec (WithLp.ofLp x) (WithLp.ofLp y)

theorem dist_synthAct_eq {m : ℕ} (g : SynthLetter K m) (u v : EuclideanSpace ℂ (Fin K)) :
    dist (synthAct K m g u) (synthAct K m g v) = dist u v := by
  cases g with
  | inl g =>
      by_cases hij : g.1 = g.2.1
      · simp only [synthAct, synthGate, if_pos hij]
        rfl
      · simp only [synthAct, synthGate, if_neg hij]
        rw [dist_eucVec, dist_eucVec_ofLp u v]
        congr 1
        have hkey : ∀ r, rotAct g.1 g.2.1 (gridAngle m g.2.2) (WithLp.ofLp u) r
            - rotAct g.1 g.2.1 (gridAngle m g.2.2) (WithLp.ofLp v) r
            = rotAct g.1 g.2.1 (gridAngle m g.2.2) (WithLp.ofLp u - WithLp.ofLp v) r := by
          intro r
          rw [rotAct_sub]
          rfl
        rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) => by rw [hkey r]),
          sum_normSq_rotAct hij]
        rfl
  | inr g =>
      simp only [synthAct, synthGate]
      rw [dist_eucVec, dist_eucVec_ofLp u v]
      congr 1
      have hkey : ∀ r, phaseAct g.1 (gridAngle m g.2) (WithLp.ofLp u) r
          - phaseAct g.1 (gridAngle m g.2) (WithLp.ofLp v) r
          = phaseAct g.1 (gridAngle m g.2) (WithLp.ofLp u - WithLp.ofLp v) r := by
        intro r
        rw [phaseAct_sub]
        rfl
      rw [Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) => by rw [hkey r]),
        sum_normSq_phaseAct]
      rfl


/-! ## Word-level isometry and the two passes -/

theorem dist_wordAct_eq {m : ℕ} :
    ∀ (w : List (SynthLetter K m)) (u v : EuclideanSpace ℂ (Fin K)),
      dist (wordAct (synthAct K m) w u) (wordAct (synthAct K m) w v) = dist u v
  | [], u, v => by simp [wordAct_nil]
  | g :: w, u, v => by
      rw [wordAct_cons, wordAct_cons, dist_synthAct_eq, dist_wordAct_eq w u v]

/-- The fixed reference state: the first computational basis vector. -/
def unitBasisFirst (K : ℕ) : Fin K → ℂ := fun r => if (r : ℕ) = 0 then 1 else 0

theorem absState_zero_eq (ψ : Fin K → ℂ) (hunit : ∑ r, ‖ψ r‖ ^ (2 : ℕ) = 1) :
    absState ψ 0 = unitBasisFirst K := absState_zero ψ hunit

/-- **The amplitude pass.** -/
theorem exists_absWord (ψ : Fin K → ℂ) (hunit : ∑ r, ‖ψ r‖ ^ (2 : ℕ) = 1) (hK : 0 < K) {m : ℕ}
    (hm : 0 < m) :
    ∀ p : ℕ, p + 1 ≤ K →
      ∃ w : List (SynthLetter K m), w.length = p ∧
        dist (wordAct (synthAct K m) w (eucVec (unitBasisFirst K))) (eucVec (absState ψ p))
          ≤ (p : ℝ) * (Real.sqrt (K : ℝ) * (2 * (2 * Real.pi / m)))
  | 0, _ => by
      refine ⟨[], rfl, ?_⟩
      rw [wordAct_nil, ← absState_zero_eq ψ hunit, dist_self]
      norm_num
  | (p + 1), hp => by
      have hplt : p + 1 < K := by omega
      have hpk : p < K := by omega
      obtain ⟨w, hwlen, hwdist⟩ := exists_absWord ψ hunit hK hm p (by omega)
      obtain ⟨i, hidef⟩ : ∃ i : Fin K, i = (⟨p, hpk⟩ : Fin K) := ⟨_, rfl⟩
      obtain ⟨j, hjdef⟩ : ∃ j : Fin K, j = (⟨p + 1, hplt⟩ : Fin K) := ⟨_, rfl⟩
      have hival : (i : ℕ) = p := by rw [hidef]
      have hjval : (j : ℕ) = p + 1 := by rw [hjdef]
      obtain ⟨q, hqc, hqs⟩ := exists_gridIndex_trig hm (rotAngle ψ i)
      refine ⟨Sum.inl (i, j, q) :: w, by rw [List.length_cons, hwlen], ?_⟩
      have hstep := rotStep ψ (i := i) (j := j) (by rw [hival, hjval])
      rw [hival] at hstep
      have hnorm : ∑ r, ‖absState ψ p r‖ ^ (2 : ℕ) = 1 := by
        rw [sum_normSq_absState ψ hK p (by omega), hunit]
      have hij : i ≠ j := by
        intro h
        rw [h, hjval] at hival
        omega
      have hgateEq : synthAct K m (Sum.inl (i, j, q)) (eucVec (absState ψ p))
          = eucVec (rotAct i j (gridAngle m q) (absState ψ p)) := by
        simp only [synthAct, synthGate, if_neg hij]
        rfl
      have hpt : ∀ r, ‖rotAct i j (gridAngle m q) (absState ψ p) r
          - rotAct i j (rotAngle ψ i) (absState ψ p) r‖ ≤ 2 * (2 * Real.pi / m) := by
        intro r
        refine le_trans (norm_rotAct_sub_le i j (gridAngle m q) (rotAngle ψ i) _ r) ?_
        rw [hnorm, Real.sqrt_one, mul_one]
        have h1 : |Real.cos (gridAngle m q) - Real.cos (rotAngle ψ i)| ≤ 2 * Real.pi / m := by
          rw [abs_sub_comm]
          exact hqc
        have h2 : |Real.sin (gridAngle m q) - Real.sin (rotAngle ψ i)| ≤ 2 * Real.pi / m := by
          rw [abs_sub_comm]
          exact hqs
        linarith
      have hsecond : dist (synthAct K m (Sum.inl (i, j, q)) (eucVec (absState ψ p)))
          (eucVec (absState ψ (p + 1)))
          ≤ Real.sqrt (K : ℝ) * (2 * (2 * Real.pi / m)) := by
        rw [hgateEq, ← hstep]
        exact dist_le_of_pointwise (by positivity) hpt
      have hfirst : dist (wordAct (synthAct K m) (Sum.inl (i, j, q) :: w)
            (eucVec (unitBasisFirst K)))
          (synthAct K m (Sum.inl (i, j, q)) (eucVec (absState ψ p)))
          ≤ (p : ℝ) * (Real.sqrt (K : ℝ) * (2 * (2 * Real.pi / m))) := by
        rw [wordAct_cons, dist_synthAct_eq]
        exact hwdist
      have htri := dist_triangle (wordAct (synthAct K m) (Sum.inl (i, j, q) :: w)
        (eucVec (unitBasisFirst K)))
        (synthAct K m (Sum.inl (i, j, q)) (eucVec (absState ψ p)))
        (eucVec (absState ψ (p + 1)))
      push_cast
      linarith [htri, hfirst, hsecond]

/-- **The phase pass.** -/
theorem exists_phWord (ψ : Fin K → ℂ) (hunit : ∑ r, ‖ψ r‖ ^ (2 : ℕ) = 1) {m : ℕ} (hm : 0 < m) :
    ∀ q : ℕ, q ≤ K →
      ∃ w : List (SynthLetter K m), w.length = q ∧
        dist (wordAct (synthAct K m) w (eucVec (phState ψ 0))) (eucVec (phState ψ q))
          ≤ (q : ℝ) * (Real.sqrt (K : ℝ) * (2 * Real.pi / m))
  | 0, _ => by
      refine ⟨[], rfl, ?_⟩
      rw [wordAct_nil, dist_self]
      norm_num
  | (q + 1), hq => by
      have hqlt : q < K := by omega
      obtain ⟨w, hwlen, hwdist⟩ := exists_phWord ψ hunit hm q (by omega)
      obtain ⟨i, hidef⟩ : ∃ i : Fin K, i = (⟨q, hqlt⟩ : Fin K) := ⟨_, rfl⟩
      have hival : (i : ℕ) = q := by rw [hidef]
      obtain ⟨t, ht⟩ := exists_gridIndex hm (Complex.arg (ψ i))
      have htexp := ht (-1) (by norm_num)
      refine ⟨Sum.inr (i, t) :: w, by rw [List.length_cons, hwlen], ?_⟩
      have hstep := phaseStep_twoLevelStateSynthesis ψ i
      rw [hival] at hstep
      have hnorm : ∑ r, ‖phState ψ q r‖ ^ (2 : ℕ) = ∑ r, ‖ψ r‖ ^ (2 : ℕ) := sum_normSq_phState ψ q
      have hgateEq : synthAct K m (Sum.inr (i, t)) (eucVec (phState ψ q))
          = eucVec (phaseAct i (gridAngle m t) (phState ψ q)) := rfl
      have hpt : ∀ r, ‖phaseAct i (gridAngle m t) (phState ψ q) r
          - phaseAct i (Complex.arg (ψ i)) (phState ψ q) r‖
          ≤ (2 * Real.pi / m) * Real.sqrt (∑ x, ‖ψ x‖ ^ (2 : ℕ)) := by
        intro r
        refine le_trans (norm_phaseAct_sub_le i (gridAngle m t) (Complex.arg (ψ i))
          (phState ψ q) r) ?_
        rw [hnorm]
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        rw [← norm_neg]
        have hrw : -(Complex.exp (((gridAngle m t : ℝ)) * Complex.I)
              - Complex.exp (((Complex.arg (ψ i) : ℝ)) * Complex.I))
            = Complex.exp ((-(Complex.arg (ψ i) * (-1)) : ℝ) * Complex.I)
              - Complex.exp ((-(gridAngle m t * (-1)) : ℝ) * Complex.I) := by
          push_cast
          ring_nf
        rw [hrw]
        exact htexp
      have hpt' : ∀ r, ‖phaseAct i (gridAngle m t) (phState ψ q) r
          - phaseAct i (Complex.arg (ψ i)) (phState ψ q) r‖ ≤ 2 * Real.pi / m := by
        intro r
        refine le_trans (hpt r) (le_of_eq ?_)
        rw [hunit, Real.sqrt_one, mul_one]
      have hsecond : dist (synthAct K m (Sum.inr (i, t)) (eucVec (phState ψ q)))
          (eucVec (phState ψ (q + 1)))
          ≤ Real.sqrt (K : ℝ) * (2 * Real.pi / m) := by
        rw [hgateEq, ← hstep]
        exact dist_le_of_pointwise (by positivity) hpt'
      have hfirst : dist (wordAct (synthAct K m) (Sum.inr (i, t) :: w)
            (eucVec (phState ψ 0)))
          (synthAct K m (Sum.inr (i, t)) (eucVec (phState ψ q)))
          ≤ (q : ℝ) * (Real.sqrt (K : ℝ) * (2 * Real.pi / m)) := by
        rw [wordAct_cons, dist_synthAct_eq]
        exact hwdist
      have htri := dist_triangle (wordAct (synthAct K m) (Sum.inr (i, t) :: w)
        (eucVec (phState ψ 0)))
        (synthAct K m (Sum.inr (i, t)) (eucVec (phState ψ q)))
        (eucVec (phState ψ (q + 1)))
      push_cast
      linarith [htri, hfirst, hsecond]


/-! ## The synthesis theorem -/

/-- **Every unit vector is reached by a word of length `2K-1` up to the grid error.** -/
theorem exists_synthesis_word (ψ : Fin K → ℂ) (hunit : ∑ r, ‖ψ r‖ ^ (2 : ℕ) = 1) (hK : 0 < K)
    {m : ℕ} (hm : 0 < m) :
    ∃ w : List (SynthLetter K m), w.length ≤ 2 * K ∧
      dist (wordAct (synthAct K m) w (eucVec (unitBasisFirst K))) (eucVec ψ)
        ≤ (3 * (K : ℝ)) * Real.sqrt (K : ℝ) * (2 * Real.pi / m) := by
  classical
  obtain ⟨wamp, hamplen, hampdist⟩ := exists_absWord ψ hunit hK hm (K - 1) (by omega)
  obtain ⟨wph, hphlen, hphdist⟩ := exists_phWord ψ hunit hm K (le_refl K)
  have hbridge : phState ψ 0 = absState ψ (K - 1) := by
    rw [phState_zero, absState_last ψ hK]
  have htop : phState ψ K = ψ := phState_of_ge ψ (le_refl K)
  refine ⟨wph ++ wamp, ?_, ?_⟩
  · rw [List.length_append, hamplen, hphlen]
    omega
  · have happ : wordAct (synthAct K m) (wph ++ wamp) (eucVec (unitBasisFirst K))
        = wordAct (synthAct K m) wph
            (wordAct (synthAct K m) wamp (eucVec (unitBasisFirst K))) := by
      rw [wordAct, wordAct, wordAct, List.foldr_append]
    rw [happ, ← htop]
    have hfirst : dist (wordAct (synthAct K m) wph
          (wordAct (synthAct K m) wamp (eucVec (unitBasisFirst K))))
        (wordAct (synthAct K m) wph (eucVec (phState ψ 0)))
        ≤ ((K - 1 : ℕ) : ℝ) * (Real.sqrt (K : ℝ) * (2 * (2 * Real.pi / m))) := by
      rw [dist_wordAct_eq, hbridge]
      exact hampdist
    have htri := dist_triangle (wordAct (synthAct K m) wph
        (wordAct (synthAct K m) wamp (eucVec (unitBasisFirst K))))
      (wordAct (synthAct K m) wph (eucVec (phState ψ 0))) (eucVec (phState ψ K))
    have hKle : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
      have : (K - 1 : ℕ) ≤ K := by omega
      exact_mod_cast this
    have hstep : (0 : ℝ) ≤ Real.sqrt (K : ℝ) * (2 * (2 * Real.pi / m)) := by positivity
    have hpi : (0 : ℝ) ≤ 2 * Real.pi / m := by positivity
    have hsq : (0 : ℝ) ≤ Real.sqrt (K : ℝ) := Real.sqrt_nonneg _
    nlinarith [htri, hfirst, hphdist, hKle, hstep, hpi, hsq]

/-- **The synthesis alphabet.**  For every tolerance there is a grid whose words of length at most
`2K` reach every unit vector of `ℂ^K` within that tolerance. -/
theorem exists_synthesis_alphabet (K : ℕ) (hK : 0 < K) {eta : ℝ} (heta : 0 < eta) :
    ∃ m : ℕ, 0 < m ∧ ∀ ψ : Fin K → ℂ, (∑ r, ‖ψ r‖ ^ (2 : ℕ) = 1) →
      ∃ w : List (SynthLetter K m), w.length ≤ 2 * K ∧
        dist (wordAct (synthAct K m) w (eucVec (unitBasisFirst K))) (eucVec ψ) ≤ eta := by
  classical
  obtain ⟨m, hmdef⟩ : ∃ m : ℕ,
    m = ⌈(3 * (K : ℝ)) * Real.sqrt (K : ℝ) * (2 * Real.pi) / eta⌉₊ + 1 := ⟨_, rfl⟩
  have hmpos : 0 < m := by
    rw [hmdef]
    omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
  have hle : (3 * (K : ℝ)) * Real.sqrt (K : ℝ) * (2 * Real.pi / m) ≤ eta := by
    rw [mul_div_assoc', div_le_iff₀ hmR]
    have hceil : (3 * (K : ℝ)) * Real.sqrt (K : ℝ) * (2 * Real.pi) / eta
        ≤ (⌈(3 * (K : ℝ)) * Real.sqrt (K : ℝ) * (2 * Real.pi) / eta⌉₊ : ℝ) := Nat.le_ceil _
    have hmge : (3 * (K : ℝ)) * Real.sqrt (K : ℝ) * (2 * Real.pi) / eta ≤ (m : ℝ) := by
      rw [hmdef]
      push_cast
      linarith [hceil]
    rw [div_le_iff₀ heta] at hmge
    linarith [hmge]
  refine ⟨m, hmpos, fun ψ hunit => ?_⟩
  obtain ⟨w, hwlen, hwdist⟩ := exists_synthesis_word ψ hunit hK hmpos
  exact ⟨w, hwlen, le_trans hwdist hle⟩

end GaloisForLFunctions.HTGeometry

end
