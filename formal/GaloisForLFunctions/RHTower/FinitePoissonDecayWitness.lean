import GaloisForLFunctions.RHTower.AtomicPoleFilterGenerator

/-!
# Finite-level decay witnesses as finite Poisson superpositions

**Theorem** (`exists_finitePoisson_decayWitness`). For every `N` there are finitely many points
`z_i = p_i + i q_i ∈ ℍ` and real weights `a_i` such that

`h(x) = Σ_i a_i (q_i / ((x − p_i)² + q_i²))^{1/2}`

(a finite superposition of `s = ½` Poisson vectors) has these properties:
* `h` is even, satisfies `h(1/x) = |x| h(x)`, and is integrable with `∫ h = 0`;
* `|e^{v/2} h(e^v)| ≤ C e^{−3|v|/2}`;
* `∫ h'(x) sin(2πm x) dx = 0` for `2 ≤ m ≤ N + 1`;
* `e^{v/2} h(e^v)` is strictly positive definite.

So every finite truncation of the decay-class (N1) condition is realized by finitely many points of
the upper half-plane. Proof:
- the atomic generators `h_{b,u}` of `AtomicPoleFilterGenerator`, with weights `≈ δ₀` as `b → ∞`;
- the density of the Whittaker cone (`closure_momentCone_arcSineMomentVec`);
- the signed-basis robustness lemma at one large `b`.

Generic tools:
- `abs_le_of_logProfile_decay`: decay of a log profile gives `|h(x)| ≲ (1 + x²)^{−1}`;
- `integral_exp_half_mul_eq_zero_of_tilt`: a tilt bound gives the vanishing `e^{v/2}` moment;
- `exists_momentCone_zero_of_uniform_approx`: uniform approximation of the Whittaker vectors gives
  an exact nonnegative relation.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Generic tools -/

/-- A decaying log profile gives `|h(x)| ≤ 2C (1 + x²)^{−1}`. -/
theorem abs_le_of_logProfile_decay {h : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C) (heven : ∀ x, h (-x) = h x)
    (h0 : h 0 = 0)
    (hprof : ∀ v, |Real.exp (v / 2) * h (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) (x : ℝ) :
    |h x| ≤ 2 * C * (1 + x ^ 2)⁻¹ := by
  have hpos : ∀ x : ℝ, 0 < x → |h x| ≤ 2 * C * (1 + x ^ 2)⁻¹ := by
    intro x hx
    set v := Real.log x
    have hev : Real.exp v = x := Real.exp_log hx
    have hP := hprof v
    rw [hev, abs_mul, abs_of_pos (Real.exp_pos _)] at hP
    have h1 : |h x| ≤ C * Real.exp (-(v / 2) - 3 * |v| / 2) := by
      have he : Real.exp (-(v / 2)) * Real.exp (v / 2) = 1 := by rw [← Real.exp_add]; simp
      calc |h x| = Real.exp (-(v / 2)) * (Real.exp (v / 2) * |h x|) := by
            rw [← mul_assoc, he, one_mul]
        _ ≤ Real.exp (-(v / 2)) * (C * Real.exp (-(3 * |v| / 2))) :=
            mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
        _ = C * Real.exp (-(v / 2) - 3 * |v| / 2) := by
            rw [mul_left_comm, ← Real.exp_add]; ring_nf
    refine h1.trans ?_
    rcases le_total 0 v with hv | hv
    · rw [abs_of_nonneg hv, show -(v / 2) - 3 * v / 2 = -(2 * v) by ring, Real.exp_neg,
        show (2 : ℝ) * v = ((2 : ℕ) : ℝ) * v by norm_num, Real.exp_nat_mul, hev]
      have hx1 : 1 ≤ x := by rw [← hev]; exact Real.one_le_exp hv
      have key : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
        rw [show 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by ring, inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc C * (x ^ 2)⁻¹ ≤ C * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left key hC
        _ = 2 * C * (1 + x ^ 2)⁻¹ := by ring
    · rw [abs_of_nonpos hv, show -(v / 2) - 3 * -v / 2 = v by ring, hev]
      have hx1 : x ≤ 1 := by rw [← hev]; exact Real.exp_le_one_iff.mpr hv
      have key : x ≤ 2 * (1 + x ^ 2)⁻¹ := by
        rw [show 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by ring, le_div_iff₀ (by positivity)]
        nlinarith
      calc C * x ≤ C * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left key hC
        _ = 2 * C * (1 + x ^ 2)⁻¹ := by ring
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have := hpos (-x) (by linarith)
    rwa [heven, neg_sq] at this
  · rw [hx, h0, abs_zero]; positivity
  · exact hpos x hx

/-- **Vanishing `e^{v/2}`-moment from a tilt bound.** If `|P(v)| ≤ C e^{−3|v|/2}` and
`|∫ e^{λv} P| ≤ D(½ − λ)` for `0 ≤ λ < ½`, then `∫ e^{v/2} P = 0`. -/
theorem integral_exp_half_mul_eq_zero_of_tilt {P : ℝ → ℝ} (hP : Continuous P) {C D : ℝ}
    (hdecay : ∀ v, |P v| ≤ C * Real.exp (-(3 * |v| / 2)))
    (htilt : ∀ l, 0 ≤ l → l < 1 / 2 → |∫ v, Real.exp (l * v) * P v| ≤ D * (1 / 2 - l)) :
    ∫ v, Real.exp (v / 2) * P v = 0 := by
  set I : ℝ → ℝ := fun l => ∫ v, Real.exp (l * v) * P v with hIdef
  have hev : ∀ᶠ l in 𝓝[<] (1 / 2 : ℝ), l ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsLT (by norm_num)
  have hzero : Tendsto I (𝓝[<] (1 / 2 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun l => D * (1 / 2 - l)) ?_ ?_
    · filter_upwards [hev] with l hl
      rw [Real.norm_eq_abs]; exact htilt l hl.1.le hl.2
    · have hc : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
      have h := hc.tendsto (1 / 2 : ℝ)
      simp only [sub_self, mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto I (𝓝[<] (1 / 2 : ℝ)) (𝓝 (I (1 / 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => C * Real.exp (-(1 * |v|))) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun l =>
        ((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v)).mul hP).aestronglyMeasurable
    · filter_upwards [hev] with l hl
      refine Eventually.of_forall fun v => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Real.exp (l * v)| ≤ Real.exp (|v| / 2) := by
        rw [abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        have := le_abs_self v
        have := neg_abs_le v
        nlinarith [hl.1, hl.2, abs_nonneg v]
      calc |Real.exp (l * v)| * |P v| ≤ Real.exp (|v| / 2) * (C * Real.exp (-(3 * |v| / 2))) :=
            mul_le_mul h1 (hdecay v) (abs_nonneg _) (Real.exp_pos _).le
        _ = C * Real.exp (-(1 * |v|)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    · have hC0 : 0 ≤ C := by
        have := (abs_nonneg (P 0)).trans (hdecay 0); simp at this; linarith
      exact (integrable_rexp_neg_mul_abs one_pos).const_mul C
    · refine Eventually.of_forall fun v => ?_
      have h := ((by fun_prop : Continuous fun l : ℝ => Real.exp (l * v) * P v).tendsto (1 / 2 : ℝ))
      exact h.mono_left nhdsWithin_le_nhds
  have hI0 : I (1 / 2) = 0 := tendsto_nhds_unique hlim hzero
  rw [hIdef] at hI0
  simp only at hI0
  rw [← hI0]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  ring_nf

/-- **Exact relations from uniform approximation.** If moment vectors `V K u` approximate the
Whittaker vectors uniformly as `K` varies, then some `V K` admits a nontrivial nonnegative relation. -/
theorem exists_momentCone_zero_of_uniform_approx (M : ℕ)
    (V : ℝ → ArcParam → (Fin (M + 1) → ℝ))
    (happ : ∀ η : ℝ, 0 < η → ∃ K : ℝ, 0 < K ∧ ∀ u, ‖V K u - arcSineMomentVec (M + 1) u‖ ≤ η) :
    ∃ K : ℝ, 0 < K ∧ ∃ L : ArcParam →₀ ℝ, (∀ u, 0 ≤ L u) ∧ L ≠ 0 ∧
      Finsupp.linearCombination ℝ (V K) L = 0 := by
  set ε : ℝ := 1 / (2 * ((M : ℝ) + 2)) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by rw [hε, div_lt_one (by positivity)]; linarith [(M.cast_nonneg : (0:ℝ) ≤ M)]
  have happrox : ∀ q : Fin (M + 1) × Bool, ∃ L : ArcParam →₀ ℝ, (∀ u, 0 ≤ L u) ∧
      ‖Finsupp.linearCombination ℝ (arcSineMomentVec (M + 1)) L - signedBasis q‖ < ε / 2 := by
    intro q
    have hmem : signedBasis q ∈ closure (momentCone (arcSineMomentVec (M + 1))) := by
      rw [closure_momentCone_arcSineMomentVec]; trivial
    obtain ⟨b, ⟨L, hL0, hLb⟩, hdist⟩ := Metric.mem_closure_iff.mp hmem (ε / 2) (by positivity)
    exact ⟨L, hL0, by rw [hLb, ← dist_eq_norm, dist_comm]; exact hdist⟩
  choose Lq hLq0 hLq using happrox
  set mass : ℝ := ∑ q, (Lq q).sum fun _ a => a with hmass
  have hmass_q : ∀ q, (Lq q).sum (fun _ a => a) ≤ mass := fun q => by
    rw [hmass]
    refine Finset.single_le_sum (f := fun q => (Lq q).sum fun _ a => a) (fun q' _ => ?_)
      (Finset.mem_univ q)
    exact Finset.sum_nonneg fun u _ => hLq0 q' u
  have hmass0 : 0 ≤ mass := (Finset.sum_nonneg fun u _ => hLq0 _ u).trans (hmass_q (0, true))
  obtain ⟨K, hK, hKapp⟩ := happ (ε / 2 / (mass + 1)) (by positivity)
  refine ⟨K, hK, ?_⟩
  set p : Fin (M + 1) × Bool → (Fin (M + 1) → ℝ) := fun q =>
    Finsupp.linearCombination ℝ (V K) (Lq q) with hp
  have hpq : ∀ q, ‖p q - signedBasis q‖ ≤ ε := by
    intro q
    have h1 := norm_linearCombination_sub_le (V := V K) (W := arcSineMomentVec (M + 1))
      (ε := ε / 2 / (mass + 1)) hKapp (hLq0 q)
    have h2 : ((Lq q).sum fun _ a => a) * (ε / 2 / (mass + 1)) ≤ ε / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have := hmass_q q
      nlinarith
    calc ‖p q - signedBasis q‖ = ‖(p q - Finsupp.linearCombination ℝ (arcSineMomentVec (M + 1))
          (Lq q)) + (Finsupp.linearCombination ℝ (arcSineMomentVec (M + 1)) (Lq q) -
            signedBasis q)‖ := by congr 1; abel
      _ ≤ ‖p q - Finsupp.linearCombination ℝ (arcSineMomentVec (M + 1)) (Lq q)‖ +
          ‖Finsupp.linearCombination ℝ (arcSineMomentVec (M + 1)) (Lq q) - signedBasis q‖ :=
          norm_add_le _ _
      _ ≤ ε := by linarith [hLq q]
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hsum⟩ :=
    mem_convexHull_iff_exists_fintype.mp (zero_mem_convexHull_of_near_signedBasis p hpq)
  choose qi hqi using hz
  refine ⟨∑ i, w i • Lq (qi i), fun u => ?_, ?_, ?_⟩
  · rw [Finsupp.finsetSum_apply]
    exact Finset.sum_nonneg fun i _ => by
      rw [Finsupp.smul_apply, smul_eq_mul]; exact mul_nonneg (hw0 i) (hLq0 _ u)
  · intro hL
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := w)
      (by rw [hw1]; norm_num)
    have hwpos : 0 < w i₀ := lt_of_le_of_ne (hw0 i₀) (Ne.symm hi₀)
    have hzero : Lq (qi i₀) = 0 := by
      ext u
      have h := congrArg (fun L : ArcParam →₀ ℝ => L u) hL
      simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
        Finsupp.coe_zero, Pi.zero_apply] at h
      have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
        mul_nonneg (hw0 i) (hLq0 (qi i) u)).mp h i₀ (Finset.mem_univ _)
      simpa [hwpos.ne'] using hall
    have hp0 : p (qi i₀) = 0 := by rw [hp]; simp only [hzero, map_zero]
    have := hpq (qi i₀)
    rw [hp0, zero_sub, norm_neg, norm_signedBasis] at this
    linarith
  · rw [map_sum]
    simp only [map_smul]
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ => by rw [← hqi i]

/-! ### Decay of the atomic generators -/

theorem abs_atomShift_le {b : ℝ} (hb : 0 ≤ b) (j : Fin 5) : |atomShift b j| ≤ 2 * b := by
  fin_cases j <;> simp [atomShift, abs_of_nonneg hb] <;> linarith

/-- `Σ_j m_j e^{σ w_j} = 0` for `σ = ±½`. -/
theorem atomWeight_edge_sum (b σ : ℝ) (hσ : σ = 1 / 2 ∨ σ = -(1 / 2)) :
    ∑ j, atomWeight b j * Real.exp (σ * atomShift b j) = 0 := by
  rw [← atomicWeight_edge b σ hσ]
  simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, mul_zero, Real.exp_zero]
  ring

/-- `Σ_j |m_j|`. -/
def atomMass (b : ℝ) : ℝ := ∑ j, |atomWeight b j|

theorem atomMass_nonneg (b : ℝ) : 0 ≤ atomMass b := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_atomicArcProfile_le_of_nonneg {b : ℝ} (hb : 0 ≤ b) (u : ArcParam) {v : ℝ}
    (hv : 0 ≤ v) :
    |atomicArcProfile b u v| ≤ 10 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) := by
  set E : ℝ → ℝ := fun t => arcPairProfile u t - arcPairTail u t with hEdef
  rw [atomicArcProfile_eq_sum]
  have hsplit : ∑ j, atomWeight b j * arcPairProfile u (v - atomShift b j) =
      ∑ j, atomWeight b j * E (v - atomShift b j) +
        ∑ j, atomWeight b j * arcPairTail u (v - atomShift b j) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [hEdef]; ring
  have hexp : Real.exp (-(3 * |v| / 2)) ≤ Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) :=
    le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_exp (by linarith))
  -- the remainder part
  have hE : |∑ j, atomWeight b j * E (v - atomShift b j)| ≤
      8 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [atomMass, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul]
    have h1 : |E (v - atomShift b j)| ≤ 8 * Real.exp (-(3 * |v - atomShift b j| / 2)) :=
      abs_arcPairProfile_sub_le u _
    have h2 := exp_neg_abs_sub_le v (atomShift b j)
    have h3 : Real.exp (3 / 2 * |atomShift b j|) ≤ Real.exp (3 * b) :=
      Real.exp_le_exp.mpr (by have := abs_atomShift_le hb j; linarith)
    calc |atomWeight b j| * |E (v - atomShift b j)|
        ≤ |atomWeight b j| * (8 * (Real.exp (-(3 * |v| / 2)) * Real.exp (3 * b))) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) (abs_nonneg _)
          have := mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-(3 * |v| / 2))).le
          linarith
      _ = 8 * |atomWeight b j| * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) := by ring
  -- the edge part
  have hT : |∑ j, atomWeight b j * arcPairTail u (v - atomShift b j)| ≤
      2 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) := by
    rcases le_or_gt (2 * b) v with hvb | hvb
    · have hz : ∑ j, atomWeight b j * arcPairTail u (v - atomShift b j) = 0 := by
        have e : ∀ j, atomWeight b j * arcPairTail u (v - atomShift b j) =
            2 * Real.sqrt (modularArcHeight u) * Real.exp (-(v / 2)) *
              (atomWeight b j * Real.exp (1 / 2 * atomShift b j)) := fun j => by
          have hj := abs_atomShift_le hb j
          have hnn : 0 ≤ v - atomShift b j := by
            have := (le_abs_self (atomShift b j)).trans hj; linarith
          simp only [arcPairTail, abs_of_nonneg hnn]
          rw [show -((v - atomShift b j) / 2) = -(v / 2) + 1 / 2 * atomShift b j by ring,
            Real.exp_add]
          ring
        simp_rw [e]
        rw [← Finset.mul_sum, atomWeight_edge_sum b (1 / 2) (Or.inl rfl), mul_zero]
      rw [hz, abs_zero]
      have := atomMass_nonneg b
      positivity
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hle : ∀ j, |atomWeight b j * arcPairTail u (v - atomShift b j)| ≤
          2 * |atomWeight b j| := fun j => by
        rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (abs_arcPairTail_le u _) (abs_nonneg _)
      refine (Finset.sum_le_sum fun j _ => hle j).trans ?_
      rw [← Finset.mul_sum, ← atomMass]
      have h1 : 1 ≤ Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) := by
        rw [← Real.exp_add, abs_of_nonneg hv]
        exact Real.one_le_exp (by linarith)
      have := atomMass_nonneg b
      nlinarith
  rw [hsplit]
  calc |∑ j, atomWeight b j * E (v - atomShift b j) +
        ∑ j, atomWeight b j * arcPairTail u (v - atomShift b j)|
      ≤ |∑ j, atomWeight b j * E (v - atomShift b j)| +
        |∑ j, atomWeight b j * arcPairTail u (v - atomShift b j)| := abs_add_le _ _
    _ ≤ 10 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) := by linarith

/-- **The atomic generators are in the decay class.** -/
theorem abs_atomicArcProfile_le {b : ℝ} (hb : 0 ≤ b) (u : ArcParam) (v : ℝ) :
    |atomicArcProfile b u v| ≤ 10 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2)) := by
  rcases le_total 0 v with hv | hv
  · exact abs_atomicArcProfile_le_of_nonneg hb u hv
  · rw [← atomicArcProfile_neg, ← abs_neg v]
    exact abs_atomicArcProfile_le_of_nonneg hb u (by linarith)

theorem atomicArcVector_zero (b : ℝ) (u : ArcParam) : atomicArcVector b u 0 = 0 := by
  have h := atomicWeight_edge b (-(1 / 2)) (Or.inr rfl)
  have key : ∀ w, dilatedArcPair u w 0 = Real.exp (-(1 / 2) * w) * arcPairVector u 0 := fun w => by
    simp only [dilatedArcPair, zero_mul]; congr 2; ring
  simp only [atomicArcVector, key, mul_zero, Real.exp_zero, one_mul]
  linear_combination arcPairVector u 0 * h

theorem abs_atomicArcVector_le {b : ℝ} (hb : 0 ≤ b) (u : ArcParam) (x : ℝ) :
    |atomicArcVector b u x| ≤
      2 * (10 * atomMass b * Real.exp (3 * b)) * (1 + x ^ 2)⁻¹ :=
  abs_le_of_logProfile_decay (by have := atomMass_nonneg b; positivity)
    (atomicArcVector_neg b u) (atomicArcVector_zero b u)
    (fun v => by rw [exp_half_mul_atomicArcVector]; exact abs_atomicArcProfile_le hb u v) x

theorem integrable_atomicArcVector {b : ℝ} (hb : 0 ≤ b) (u : ArcParam) :
    Integrable (atomicArcVector b u) :=
  (integrable_inv_one_add_sq.const_mul _).mono' (continuous_atomicArcVector b u).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_atomicArcVector_le hb u x)

/-! ### Zero mean -/

theorem integrable_exp_mul_arcPairProfile (u : ArcParam) {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    Integrable fun v => Real.exp (l * v) * arcPairProfile u v := by
  have hκ : 0 < 1 / 2 - l := by linarith
  refine ((integrable_rexp_neg_mul_abs hκ).const_mul 10).mono'
    ((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v)).mul
      (continuous_arcPairProfile u)).aestronglyMeasurable (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |Real.exp (l * v)| * |arcPairProfile u v|
      ≤ Real.exp (l * |v|) * (10 * Real.exp (-(|v| / 2))) :=
        mul_le_mul (abs_exp_mul_le hl0) (abs_arcPairProfile_le_exp u v) (abs_nonneg _)
          (Real.exp_pos _).le
    _ = 10 * Real.exp (-((1 / 2 - l) * |v|)) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

theorem abs_integral_exp_mul_arcPairProfile_le (u : ArcParam) {l : ℝ} (hl0 : 0 ≤ l)
    (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcPairProfile u v| ≤ 20 / (1 / 2 - l) := by
  have hκ : 0 < 1 / 2 - l := by linarith
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ v, |Real.exp (l * v) * arcPairProfile u v|
      ≤ ∫ v, 10 * Real.exp (-((1 / 2 - l) * |v|)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun v => abs_nonneg _)
          ((integrable_rexp_neg_mul_abs hκ).const_mul 10) (Eventually.of_forall fun v => ?_)
        dsimp only
        rw [abs_mul]
        calc |Real.exp (l * v)| * |arcPairProfile u v|
            ≤ Real.exp (l * |v|) * (10 * Real.exp (-(|v| / 2))) :=
              mul_le_mul (abs_exp_mul_le hl0) (abs_arcPairProfile_le_exp u v) (abs_nonneg _)
                (Real.exp_pos _).le
          _ = 10 * Real.exp (-((1 / 2 - l) * |v|)) := by
              rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    _ = 20 / (1 / 2 - l) := by
        rw [integral_const_mul, integral_rexp_neg_mul_abs hκ]; ring

theorem integral_exp_mul_arcPairProfile_sub (u : ArcParam) (l w : ℝ) :
    ∫ v, Real.exp (l * v) * arcPairProfile u (v - w) =
      Real.exp (l * w) * ∫ v, Real.exp (l * v) * arcPairProfile u v := by
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v => Real.exp (l * v) * arcPairProfile u (v - w)) w, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [add_sub_cancel_right, show l * (v + w) = l * w + l * v by ring, Real.exp_add]; ring

theorem one_sub_cosh_div_le {b l : ℝ} (hb : 0 ≤ b) (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2) :
    0 ≤ 1 - Real.cosh (l * b) / Real.cosh (b / 2) ∧
      1 - Real.cosh (l * b) / Real.cosh (b / 2) ≤ b * (1 / 2 - l) := by
  have hC := Real.cosh_pos (b / 2)
  constructor
  · rw [sub_nonneg, div_le_one hC, Real.cosh_le_cosh, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    nlinarith
  · have hratio : Real.exp (-(b * (1 / 2 - l))) * Real.cosh (b / 2) ≤ Real.cosh (l * b) := by
      rw [Real.cosh_eq, Real.cosh_eq, mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
      have h1 : -(b * (1 / 2 - l)) + b / 2 = l * b := by ring
      have h2 : Real.exp (-(b * (1 / 2 - l)) + -(b / 2)) ≤ Real.exp (-(l * b)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      rw [h1]
      linarith
    have h3 : Real.exp (-(b * (1 / 2 - l))) ≤ Real.cosh (l * b) / Real.cosh (b / 2) := by
      rw [le_div_iff₀ hC]; exact hratio
    have h4 := Real.add_one_le_exp (-(b * (1 / 2 - l)))
    linarith

/-- **Zero mean of the atomic generators.** -/
theorem integral_atomicArcVector_eq_zero {b : ℝ} (hb : 0 ≤ b) (u : ArcParam) :
    ∫ x, atomicArcVector b u x = 0 := by
  have heven : ∀ x, atomicArcVector b u |x| = atomicArcVector b u x := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, atomicArcVector_neg]
  have h1 : ∫ x, atomicArcVector b u x = 2 * ∫ x in Ioi 0, atomicArcVector b u x := by
    rw [← integral_comp_abs (f := atomicArcVector b u)]
    exact integral_congr_ae (Eventually.of_forall fun x => (heven x).symm)
  rw [h1, setIntegral_Ioi_eq_integral_exp_mul]
  have h2 : ∀ v, Real.exp v * atomicArcVector b u (Real.exp v) =
      Real.exp (v / 2) * atomicArcProfile b u v := fun v => by
    rw [← exp_half_mul_atomicArcVector, ← mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h2]
  rw [integral_exp_half_mul_eq_zero_of_tilt (continuous_atomicArcProfile b u)
    (abs_atomicArcProfile_le hb u) (D := 20 * b ^ 2) ?_, mul_zero]
  intro l hl0 hl
  have hκ : 0 < 1 / 2 - l := by linarith
  have hi : ∀ w, Integrable fun v => Real.exp (l * v) * arcPairProfile u (v - w) := fun w => by
    have h := (integrable_exp_mul_arcPairProfile u hl0 hl).comp_sub_right w
    refine (h.const_mul (Real.exp (l * w))).congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring
  have e : ∀ v, Real.exp (l * v) * atomicArcProfile b u v =
      ∑ j, atomWeight b j * (Real.exp (l * v) * arcPairProfile u (v - atomShift b j)) := fun v => by
    rw [atomicArcProfile_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => (hi _).const_mul _]
  simp_rw [integral_const_mul, integral_exp_mul_arcPairProfile_sub]
  have hsum : ∑ j, atomWeight b j * (Real.exp (l * atomShift b j) *
      ∫ v, Real.exp (l * v) * arcPairProfile u v) =
      (1 - Real.cosh (l * b) / Real.cosh (b / 2)) ^ 2 *
        ∫ v, Real.exp (l * v) * arcPairProfile u v := by
    rw [← atomicWeight_exp]
    simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, mul_zero, Real.exp_zero]
    ring
  rw [hsum, abs_mul, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨hlo, hhi⟩ := one_sub_cosh_div_le hb hl0 hl.le
  have hQ := abs_integral_exp_mul_arcPairProfile_le u hl0 hl
  calc (1 - Real.cosh (l * b) / Real.cosh (b / 2)) ^ 2 * |∫ v, Real.exp (l * v) * arcPairProfile u v|
      ≤ (b * (1 / 2 - l)) ^ 2 * (20 / (1 / 2 - l)) :=
        mul_le_mul (pow_le_pow_left₀ hlo hhi 2) hQ (abs_nonneg _) (sq_nonneg _)
    _ = 20 * b ^ 2 * (1 / 2 - l) := by field_simp

/-! ### Moments -/

theorem integrable_atomicArcDeriv (b : ℝ) (u : ArcParam) : Integrable (atomicArcDeriv b u) := by
  have h := integrable_dilatedArcPairDeriv u
  unfold atomicArcDeriv
  exact (((h 0).const_mul _).add (((h b).add (h (-b))).const_mul _)).add
    (((h (2 * b)).add (h (-(2 * b)))).const_mul _)

/-- **The atomic sine moments.** -/
theorem integral_atomicArcDeriv_mul_sin (b : ℝ) (u : ArcParam) {c : ℝ} (hc : 0 < c) :
    ∫ x, atomicArcDeriv b u x * Real.sin (c * x) =
      ∑ j, atomWeight b j * (Real.exp (-(atomShift b j / 2)) *
        arcPairSineMoment u (c * Real.exp (atomShift b j))) := by
  have hi : ∀ w, Integrable fun x => dilatedArcPairDeriv u w x * Real.sin (c * x) := fun w =>
    (integrable_dilatedArcPairDeriv u w).mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : ∀ x, atomicArcDeriv b u x * Real.sin (c * x) =
      ∑ j, atomWeight b j * (dilatedArcPairDeriv u (atomShift b j) x * Real.sin (c * x)) :=
    fun x => by
      simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.head_cons, Matrix.tail_cons, atomicArcDeriv]
      ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => (hi _).const_mul _]
  exact Finset.sum_congr rfl fun j _ => by
    rw [integral_const_mul, integral_dilatedArcPairDeriv_mul_sin u _ hc]

/-- **Uniform error of the atomic moments**: within `4√(π/2) √c (2/C + 1/C²)` of `J_u(c)`. -/
theorem abs_integral_atomicArcDeriv_mul_sin_sub_le (b : ℝ) (u : ArcParam) {c : ℝ} (hc : 0 < c) :
    |(∫ x, atomicArcDeriv b u x * Real.sin (c * x)) - arcPairSineMoment u c| ≤
      4 * Real.sqrt (Real.pi / 2) * Real.sqrt c *
        (2 / Real.cosh (b / 2) + 1 / Real.cosh (b / 2) ^ 2) := by
  rw [integral_atomicArcDeriv_mul_sin b u hc]
  set B := 4 * Real.sqrt (Real.pi / 2) * Real.sqrt c
  have hB := abs_exp_mul_arcPairSineMoment_le u hc
  have hC := Real.cosh_pos (b / 2)
  set F : ℝ → ℝ := fun w => Real.exp (-(w / 2)) * arcPairSineMoment u (c * Real.exp w) with hF
  have h0 : F 0 = arcPairSineMoment u c := by simp [hF]
  have hsum : ∑ j, atomWeight b j * F (atomShift b j) - arcPairSineMoment u c =
      (atomW0 b - 1) * F 0 + atomW1 b * (F b + F (-b)) +
        atomW2 b * (F (2 * b) + F (-(2 * b))) := by
    simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
    rw [← h0]; ring
  change |∑ j, atomWeight b j * F (atomShift b j) - arcPairSineMoment u c| ≤ _
  rw [hsum]
  have hw0 : atomW0 b - 1 = 1 / (2 * Real.cosh (b / 2) ^ 2) := by unfold atomW0; ring
  have hFb : ∀ w, |F w| ≤ B := fun w => hB w
  have hB0 : 0 ≤ B := by positivity
  calc |(atomW0 b - 1) * F 0 + atomW1 b * (F b + F (-b)) + atomW2 b * (F (2 * b) + F (-(2 * b)))|
      ≤ |atomW0 b - 1| * |F 0| + |atomW1 b| * (|F b| + |F (-b)|) +
          |atomW2 b| * (|F (2 * b)| + |F (-(2 * b))|) := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [abs_mul]
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ ≤ |atomW0 b - 1| * B + |atomW1 b| * (B + B) + |atomW2 b| * (B + B) := by
        gcongr <;> exact hFb _
    _ = B * (2 / Real.cosh (b / 2) + 1 / Real.cosh (b / 2) ^ 2) := by
        rw [hw0, atomW1, atomW2, abs_of_pos (by positivity), abs_neg, abs_of_pos (by positivity),
          abs_of_pos (by positivity)]
        field_simp; ring

/-! ### Assembly -/

/-- The atomic moment vector `(∫ h_{b,u}' sin(2π(i+2)x) dx)_{i < N}`. -/
def atomicSineMomentVec (N : ℕ) (b : ℝ) (u : ArcParam) : Fin N → ℝ :=
  fun i => ∫ x, atomicArcDeriv b u x * Real.sin (arcFreq (i + 1) * x)

theorem norm_atomicSineMomentVec_sub_le (N : ℕ) (b : ℝ) (u : ArcParam) :
    ‖atomicSineMomentVec N b u - arcSineMomentVec N u‖ ≤
      4 * Real.sqrt (Real.pi / 2) * Real.sqrt (arcFreq N) *
        (2 / Real.cosh (b / 2) + 1 / Real.cosh (b / 2) ^ 2) := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  simp only [Pi.sub_apply, atomicSineMomentVec, arcSineMomentVec]
  refine (abs_integral_atomicArcDeriv_mul_sin_sub_le b u (arcFreq_pos _)).trans ?_
  gcongr
  exact arcFreq_le_arcFreq (by omega)

theorem exists_pos_atomError_lt (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ b : ℝ, 0 < b ∧ B * (2 / Real.cosh (b / 2) + 1 / Real.cosh (b / 2) ^ 2) ≤ η := by
  have ht : Tendsto (fun b : ℝ => 6 * |B| * Real.exp (-(b / 2))) atTop (𝓝 (6 * |B| * 0)) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const two_pos)).const_mul _
  rw [mul_zero] at ht
  obtain ⟨b, hb1, hb0⟩ := ((ht.eventually (gt_mem_nhds hη)).and (eventually_gt_atTop 0)).exists
  refine ⟨b, hb0, ?_⟩
  have hC1 : 1 ≤ Real.cosh (b / 2) := Real.one_le_cosh _
  have hC : Real.exp (b / 2) / 2 ≤ Real.cosh (b / 2) := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-(b / 2))]
  have hinv : 1 / Real.cosh (b / 2) ≤ 2 * Real.exp (-(b / 2)) := by
    rw [div_le_iff₀ (by positivity), Real.exp_neg]
    have := Real.exp_pos (b / 2)
    calc (1 : ℝ) = 2 * (Real.exp (b / 2))⁻¹ * (Real.exp (b / 2) / 2) := by field_simp
      _ ≤ 2 * (Real.exp (b / 2))⁻¹ * Real.cosh (b / 2) := by gcongr
  have hsq : 1 / Real.cosh (b / 2) ^ 2 ≤ 1 / Real.cosh (b / 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h3 : 2 / Real.cosh (b / 2) + 1 / Real.cosh (b / 2) ^ 2 ≤ 6 * Real.exp (-(b / 2)) := by
    have : 2 / Real.cosh (b / 2) = 2 * (1 / Real.cosh (b / 2)) := by ring
    linarith
  have h4 : 0 ≤ 2 / Real.cosh (b / 2) + 1 / Real.cosh (b / 2) ^ 2 := by positivity
  calc B * (2 / Real.cosh (b / 2) + 1 / Real.cosh (b / 2) ^ 2)
      ≤ |B| * (2 / Real.cosh (b / 2) + 1 / Real.cosh (b / 2) ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self B) h4
    _ ≤ |B| * (6 * Real.exp (-(b / 2))) := mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = 6 * |B| * Real.exp (-(b / 2)) := by ring
    _ ≤ η := hb1.le

theorem exists_atomicCombination (M : ℕ) :
    ∃ b : ℝ, 0 < b ∧ ∃ L : ArcParam →₀ ℝ, (∀ u, 0 ≤ L u) ∧ L ≠ 0 ∧
      Finsupp.linearCombination ℝ (atomicSineMomentVec (M + 1) b) L = 0 :=
  exists_momentCone_zero_of_uniform_approx M (fun b u => atomicSineMomentVec (M + 1) b u)
    fun η hη => by
      obtain ⟨b, hb, hbη⟩ := exists_pos_atomError_lt
        (4 * Real.sqrt (Real.pi / 2) * Real.sqrt (arcFreq (M + 1))) hη
      exact ⟨b, hb, fun u => (norm_atomicSineMomentVec_sub_le (M + 1) b u).trans hbη⟩

/-! ### Finite Poisson representation -/

/-- The `s = ½` Poisson vector `(q/((x − p)² + q²))^{1/2}` of the point `p + iq`. -/
def poissonVector (z : ℝ × ℝ) (x : ℝ) : ℝ := (z.2 / ((x - z.1) ^ 2 + z.2 ^ 2)) ^ (1 / 2 : ℝ)

/-- Dilation of a Poisson vector: `e^{−w/2} φ_{c+iy}(x e^{−w}) = φ_{e^w c + i e^w y}(x)`. -/
theorem exp_mul_poissonVector_dilate {y : ℝ} (hy : 0 < y) (c w x : ℝ) :
    Real.exp (-(w / 2)) * poissonVector (c, y) (x * Real.exp (-w)) =
      poissonVector (Real.exp w * c, Real.exp w * y) x := by
  unfold poissonVector
  simp only
  have hZ : 0 < (x - Real.exp w * c) ^ 2 + (Real.exp w * y) ^ 2 := by positivity
  have hew : Real.exp w * Real.exp (-w) = 1 := by rw [← Real.exp_add]; simp
  have e1 : (x * Real.exp (-w) - c) ^ 2 + y ^ 2 =
      Real.exp (-w) ^ 2 * ((x - Real.exp w * c) ^ 2 + (Real.exp w * y) ^ 2) := by
    linear_combination (c * (2 * Real.exp (-w) * x - c - Real.exp (-w) * Real.exp w * c) -
      y ^ 2 * (Real.exp (-w) * Real.exp w + 1)) * hew
  have e2 : y / ((x * Real.exp (-w) - c) ^ 2 + y ^ 2) = Real.exp w *
      (Real.exp w * y / ((x - Real.exp w * c) ^ 2 + (Real.exp w * y) ^ 2)) := by
    rw [e1, Real.exp_neg]
    field_simp
  rw [e2, Real.mul_rpow (Real.exp_pos w).le (by positivity), ← mul_assoc]
  have e3 : Real.exp (-(w / 2)) * Real.exp w ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.exp_mul, ← Real.exp_add]; ring_nf; simp
  rw [e3, one_mul]

theorem arcPointVector_eq_poissonVector (u : ArcParam) (x : ℝ) :
    arcPointVector u x = poissonVector ((u : ℝ), modularArcHeight u) x := rfl

/-- The arc point `e^w(±u + iy)`. -/
def arcDilatedPoint (u : ArcParam) (w : ℝ) (s : Bool) : ℝ × ℝ :=
  (Real.exp w * (if s then (u : ℝ) else -(u : ℝ)), Real.exp w * modularArcHeight u)

theorem dilatedArcPair_eq_sum_poisson (u : ArcParam) (w x : ℝ) :
    dilatedArcPair u w x = ∑ s : Bool, poissonVector (arcDilatedPoint u w s) x := by
  have hy := modularArcHeight_pos u.2
  rw [Fintype.sum_bool]
  unfold dilatedArcPair arcPairVector
  rw [mul_add, arcPointVector_eq_poissonVector, arcPointVector_eq_poissonVector,
    exp_mul_poissonVector_dilate hy, show modularArcHeight (arcNeg u) = modularArcHeight u from
      modularArcHeight_neg u, exp_mul_poissonVector_dilate hy]
  rfl

theorem atomicArcVector_eq_sum (b : ℝ) (u : ArcParam) (x : ℝ) :
    atomicArcVector b u x = ∑ j, atomWeight b j * dilatedArcPair u (atomShift b j) x := by
  simp only [Fin.sum_univ_five, atomWeight, atomShift, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, atomicArcVector]
  ring

/-! ### The theorem -/

/-- **Finite-level decay-class witnesses as finite Poisson superpositions.** -/
theorem exists_finitePoisson_decayWitness (N : ℕ) :
    ∃ h h' : ℝ → ℝ,
      (∃ (ι : Type) (_ : Fintype ι) (a : ι → ℝ) (p : ι → ℝ × ℝ), (∀ i, 0 < (p i).2) ∧
        ∀ x, h x = ∑ i, a i * poissonVector (p i) x) ∧
      (∀ x, HasDerivAt h (h' x) x) ∧ Integrable h ∧ Integrable h' ∧
      (∀ x, h (-x) = h x) ∧ (∀ x, x ≠ 0 → h (1 / x) = |x| * h x) ∧ ∫ x, h x = 0 ∧
      (∃ C, ∀ v, |Real.exp (v / 2) * h (Real.exp v)| ≤ C * Real.exp (-(3 * |v| / 2))) ∧
      (∀ n < N, ∫ x, h' x * Real.sin (arcFreq (n + 1) * x) = 0) ∧
      ∀ τ : ℝ, 0 < ∫ v, Real.cos (τ * v) * (Real.exp (v / 2) * h (Real.exp v)) := by
  obtain ⟨b, hb, L, hL0, hL, hmom⟩ := exists_atomicCombination N
  set h : ℝ → ℝ := fun x => ∑ u ∈ L.support, L u * atomicArcVector b u x with hh
  set h' : ℝ → ℝ := fun x => ∑ u ∈ L.support, L u * atomicArcDeriv b u x with hh'
  refine ⟨h, h', ?_, fun x => ?_, ?_, ?_, fun x => ?_, fun x hx => ?_, ?_,
    ⟨(∑ u ∈ L.support, L u) * (10 * atomMass b * Real.exp (3 * b)), fun v => ?_⟩,
    fun n hn => ?_, fun τ => ?_⟩
  · refine ⟨L.support × Fin 5 × Bool, inferInstance,
      fun i => L i.1 * atomWeight b i.2.1, fun i => arcDilatedPoint i.1 (atomShift b i.2.1) i.2.2,
      fun i => by
        simp only [arcDilatedPoint]
        exact mul_pos (Real.exp_pos _) (modularArcHeight_pos (i.1 : ArcParam).2), fun x => ?_⟩
    rw [Fintype.sum_prod_type, hh]
    simp only
    rw [← Finset.sum_coe_sort L.support]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Fintype.sum_prod_type, atomicArcVector_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dilatedArcPair_eq_sum_poisson, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  · exact HasDerivAt.fun_sum fun u _ => (hasDerivAt_atomicArcVector b u x).const_mul (L u)
  · exact integrable_finsetSum _ fun u _ => (integrable_atomicArcVector hb.le u).const_mul (L u)
  · exact integrable_finsetSum _ fun u _ => (integrable_atomicArcDeriv b u).const_mul (L u)
  · exact Finset.sum_congr rfl fun u _ => by rw [atomicArcVector_neg]
  · simp only [hh]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [atomicArcVector_inv b u hx]; ring
  · rw [integral_finsetSum _ fun u _ => (integrable_atomicArcVector hb.le u).const_mul (L u)]
    exact Finset.sum_eq_zero fun u _ => by
      rw [integral_const_mul, integral_atomicArcVector_eq_zero hb.le u, mul_zero]
  · simp only [hh]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [show Real.exp (v / 2) * (L u * atomicArcVector b u (Real.exp v)) =
      L u * (Real.exp (v / 2) * atomicArcVector b u (Real.exp v)) by ring,
      exp_half_mul_atomicArcVector, abs_mul, abs_of_nonneg (hL0 u), mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_atomicArcProfile_le hb.le u v) (hL0 u)
  · have hm := congrArg (fun x : Fin (N + 1) → ℝ => x ⟨n, by omega⟩) hmom
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.zero_apply, atomicSineMomentVec] at hm
    simp only [hh']
    simp_rw [Finset.sum_mul]
    rw [integral_finsetSum _ fun u _ => ?_]
    · rw [← hm]
      exact Finset.sum_congr rfl fun u _ => by
        simp_rw [mul_assoc]; rw [integral_const_mul]
    · simp_rw [mul_assoc]
      exact ((integrable_atomicArcDeriv b u).mul_bdd (by fun_prop)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)).const_mul (L u)
  · have hint : ∀ u, Integrable fun v => Real.cos (τ * v) * atomicArcProfile b u v := fun u => by
      refine ((integrable_rexp_neg_mul_abs (by norm_num : (0:ℝ) < 3 / 2)).const_mul
        (10 * atomMass b * Real.exp (3 * b))).mono' ((by fun_prop : Continuous fun v : ℝ =>
          Real.cos (τ * v)).mul (continuous_atomicArcProfile b u)).aestronglyMeasurable
        (Eventually.of_forall fun v => ?_)
      rw [Real.norm_eq_abs, abs_mul, show 3 / 2 * |v| = 3 * |v| / 2 by ring]
      calc |Real.cos (τ * v)| * |atomicArcProfile b u v|
          ≤ 1 * (10 * atomMass b * Real.exp (3 * b) * Real.exp (-(3 * |v| / 2))) :=
            mul_le_mul (Real.abs_cos_le_one _) (abs_atomicArcProfile_le hb.le u v) (abs_nonneg _)
              zero_le_one
        _ = _ := one_mul _
    have e : ∀ v, Real.cos (τ * v) * (Real.exp (v / 2) * h (Real.exp v)) =
        ∑ u ∈ L.support, L u * (Real.cos (τ * v) * atomicArcProfile b u v) := fun v => by
      simp only [hh]
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [← exp_half_mul_atomicArcVector]; ring
    simp_rw [e]
    rw [integral_finsetSum _ fun u _ => (hint u).const_mul _]
    refine Finset.sum_pos (fun u hu => ?_) (Finsupp.support_nonempty_iff.mpr hL)
    rw [integral_const_mul]
    exact mul_pos (lt_of_le_of_ne (hL0 u) (Ne.symm (Finsupp.mem_support_iff.mp hu)))
      (integral_cos_mul_atomicArcProfile_pos hb u τ)

end

end RHTower
