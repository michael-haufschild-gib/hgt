import GaloisForLFunctions.RHTower.TraceHankelConverse
import GaloisForLFunctions.HTGeometry.RealQuadraticMargin

namespace RHTower

open scoped ComplexConjugate
open Complex Filter Matrix Polynomial Topology

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Entrywise convergence preserves negative definiteness of a real finite matrix. -/
theorem eventually_realQuad_neg_of_entrywise_tendsto
    {k : ℕ} (G : ℕ → Matrix (Fin k) (Fin k) ℝ)
    (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ x : Fin k → ℝ, x ≠ 0 → realQuad A x < 0)
    (hconv : ∀ j l, Tendsto (fun n => G n j l) atTop (𝓝 (A j l))) :
    ∀ᶠ n in atTop, ∀ x : Fin k → ℝ, x ≠ 0 → realQuad (G n) x < 0 := by
  obtain ⟨δ, hδ, hmargin⟩ := exists_margin_of_negDef A hA
  let ε : ℝ := δ / (2 * ((k : ℝ) ^ 2 + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hsmall : ε * (k : ℝ) ^ 2 < δ := by
    dsimp [ε]
    rw [div_mul_eq_mul_div]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * ((k : ℝ) ^ 2 + 1))]
    nlinarith [sq_nonneg (k : ℝ), hδ]
  have hall' : ∀ᶠ n in atTop, ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ∀ l ∈ (Finset.univ : Finset (Fin k)), |G n j l - A j l| ≤ ε := by
    rw [Finset.eventually_all]
    intro j _hj
    rw [Finset.eventually_all]
    intro l _hl
    exact (hconv j l).eventually (Metric.ball_mem_nhds _ hε) |>.mono fun n hn => by
      simpa [Real.dist_eq] using le_of_lt hn
  filter_upwards [hall'] with n hn
  exact negDef_of_entrywise_close hε.le hmargin
    (fun j l => hn j (Finset.mem_univ _) l (Finset.mem_univ _)) hsmall

theorem realQuad_diagonal_neg {k : ℕ} (d : Fin k → ℝ) (hd : ∀ j, d j < 0)
    (x : Fin k → ℝ) (hx : x ≠ 0) :
    realQuad (Matrix.diagonal d) x < 0 := by
  classical
  have hquad : realQuad (Matrix.diagonal d) x = ∑ i, d i * x i * x i := by
    rw [realQuad]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
    · intro j _hj hji
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hji)]
    · simp
  rw [hquad]
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  have hterm : ∀ j, d j * x j * x j ≤ 0 := by
    intro j
    nlinarith [hd j, sq_nonneg (x j)]
  have hjterm : d j₀ * x j₀ * x j₀ < 0 := by
    have hxpos : 0 < x j₀ ^ 2 := sq_pos_of_ne_zero hj₀
    nlinarith [hd j₀]
  have hsplit := Finset.add_sum_erase Finset.univ (fun j => d j * x j * x j)
    (Finset.mem_univ j₀)
  have hrest : ∑ j ∈ Finset.univ.erase j₀, d j * x j * x j ≤ 0 :=
    Finset.sum_nonpos fun j _ => hterm j
  rw [← hsplit]
  linarith

/-- Conjugate-folded trace--Hankel polarization. -/
def foldedTraceHankelGram {ι : Type*} (lam : ι → ℂ)
    (p q : Polynomial ℝ) : ℝ :=
  2 * (∑' i : ι, lam i * evalRealPolynomial p (lam i) *
    evalRealPolynomial q (lam i)).re

/-- A finite packet of distinct nonreal conjugation folds forces a simultaneous negative
trace--Hankel Gram block in the full summable spectrum. -/
theorem exists_foldedTraceHankelGram_negativePacket
    {ι : Type*} (lam : ι → ℂ)
    (hne : ∀ i, lam i ≠ 0)
    (hfinite : ∀ {r : ℝ}, 0 < r → {i : ι | r ≤ ‖lam i‖}.Finite)
    (hsum : Summable lam)
    (horbit : ∀ i j, i ≠ j →
      lam i ≠ lam j ∧ lam i ≠ (starRingEnd ℂ) (lam j))
    {k : ℕ} (s : Fin k → ι) (hs : Function.Injective s)
    (him : ∀ j, (lam (s j)).im ≠ 0) :
    ∃ q : Fin k → Polynomial ℝ,
      LinearIndependent ℝ q ∧
      ∀ x : Fin k → ℝ, x ≠ 0 →
        realQuad (fun j l => foldedTraceHankelGram lam (q j) (q l)) x < 0 := by
  classical
  let α : Fin k → ℂ := fun j => lam (s j)
  let c : Fin k → ℂ := fun j => Classical.choose (exists_phase_sq_re_neg (him j))
  have hc (j : Fin k) : (α j * c j ^ 2).re < 0 := by
    exact Classical.choose_spec (exists_phase_sq_re_neg (him j))
  have hcne (j : Fin k) : c j ≠ 0 := by
    intro hz
    have hcj := hc j
    rw [hz, zero_pow (by omega), mul_zero, Complex.zero_re] at hcj
    exact (lt_irrefl 0) hcj
  let outer : Fin k → Finset ι := fun j =>
    (hfinite (r := ‖α j‖) (norm_pos_iff.mpr (hne (s j)))).toFinset
  let selected : Finset ℂ := Finset.univ.image α
  let F : Fin k → Finset ℂ := fun j => (outer j).image lam ∪ selected
  let qn : ℕ → Fin k → Polynomial ℝ := fun n j =>
    phaseCorrectedSeparatorPolynomial (F j) (α j) (c j) n
  have hevalTarget (n : ℕ) (j : Fin k) :
      evalRealPolynomial (qn n j) (α j) = c j := by
    exact eval_phaseCorrectedSeparatorPolynomial_target (hne (s j)) (him j) n
  have hevalLimit (j : Fin k) (i : ι) :
      Tendsto (fun n => evalRealPolynomial (qn n j) (lam i)) atTop
        (𝓝 (if i = s j then c j else 0)) := by
    by_cases hi : i = s j
    · subst i
      simpa [α] using tendsto_const_nhds.congr' (Eventually.of_forall fun n =>
        (hevalTarget n j).symm)
    · have hiα : lam i ≠ α j := by
        exact (horbit i (s j) hi).1
      have hic : lam i ≠ (starRingEnd ℂ) (α j) := by
        exact (horbit i (s j) hi).2
      by_cases houter : ‖α j‖ ≤ ‖lam i‖
      · have hiOuter : i ∈ outer j := by
          simp only [outer, Set.Finite.mem_toFinset]
          exact houter
        have hiF : lam i ∈ F j := by
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiOuter, rfl⟩)
        have hzero (n : ℕ) : evalRealPolynomial (qn n j) (lam i) = 0 :=
          eval_phaseCorrectedSeparatorPolynomial_outer_zero hiF hiα hic n
        simpa [hi] using tendsto_const_nhds.congr'
          (Eventually.of_forall fun n => (hzero n).symm)
      · have hinner : ‖lam i‖ < ‖α j‖ := lt_of_not_ge houter
        have ht := tendsto_eval_phaseCorrectedSeparatorPolynomial_zero
          (F := F j) (c := c j) (hne (s j)) (him j) hinner
        simpa [qn, hi] using ht
  let C : Fin k → ℝ := fun j => phaseCorrectedSeparatorNormBound (F j) (α j) (c j)
  have hC (j : Fin k) : 0 ≤ C j :=
    phaseCorrectedSeparatorNormBound_nonneg (F j) (him j)
  have hevalBound (n : ℕ) (j : Fin k) (i : ι) :
      ‖evalRealPolynomial (qn n j) (lam i)‖ ≤ C j := by
    by_cases hle : ‖lam i‖ ≤ ‖α j‖
    · exact norm_eval_phaseCorrectedSeparatorPolynomial_le
        (F := F j) (c := c j) (hne (s j)) (him j) hle n
    · have houter : ‖α j‖ ≤ ‖lam i‖ := le_of_not_ge hle
      have hiOuter : i ∈ outer j := by
        simp only [outer, Set.Finite.mem_toFinset]
        exact houter
      have hiF : lam i ∈ F j :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiOuter, rfl⟩)
      have hiα : lam i ≠ α j := by
        intro h
        apply hle
        rw [h]
      have hic : lam i ≠ (starRingEnd ℂ) (α j) := by
        intro h
        apply hle
        rw [h, norm_conj]
      rw [eval_phaseCorrectedSeparatorPolynomial_outer_zero hiF hiα hic n, norm_zero]
      exact hC j
  let G : ℕ → Matrix (Fin k) (Fin k) ℝ := fun n j l =>
    foldedTraceHankelGram lam (qn n j) (qn n l)
  let d : Fin k → ℝ := fun j => 2 * (α j * c j ^ 2).re
  let D : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal d
  have hconv (j l : Fin k) : Tendsto (fun n => G n j l) atTop (𝓝 (D j l)) := by
    let f : ℕ → ι → ℂ := fun n i =>
      lam i * evalRealPolynomial (qn n j) (lam i) *
        evalRealPolynomial (qn n l) (lam i)
    let g : ι → ℂ := fun i =>
      lam i * (if i = s j then c j else 0) * (if i = s l then c l else 0)
    have hpointwise (i : ι) : Tendsto (fun n => f n i) atTop (𝓝 (g i)) := by
      have hp := (hevalLimit j i).mul (hevalLimit l i)
      have hm := hp.const_mul (lam i)
      simpa only [f, g, mul_assoc] using hm
    let B : ℝ := C j * C l
    have hB : 0 ≤ B := mul_nonneg (hC j) (hC l)
    let bound : ι → ℝ := fun i => B * ‖lam i‖
    have hboundSum : Summable bound := hsum.norm.mul_left B
    have hdom : ∀ n i, ‖f n i‖ ≤ bound i := by
      intro n i
      calc
        ‖f n i‖ = ‖lam i‖ * ‖evalRealPolynomial (qn n j) (lam i)‖ *
            ‖evalRealPolynomial (qn n l) (lam i)‖ := by simp [f]
        _ ≤ ‖lam i‖ * C j * C l := by
          calc
            ‖lam i‖ * ‖evalRealPolynomial (qn n j) (lam i)‖ *
                ‖evalRealPolynomial (qn n l) (lam i)‖
                ≤ ‖lam i‖ * C j *
                    ‖evalRealPolynomial (qn n l) (lam i)‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hevalBound n j i) (norm_nonneg _))
                    (norm_nonneg _)
            _ ≤ ‖lam i‖ * C j * C l := by
                  exact mul_le_mul_of_nonneg_left (hevalBound n l i)
                    (mul_nonneg (norm_nonneg _) (hC j))
        _ = bound i := by simp [bound, B]; ring
    have htsum : Tendsto (fun n => ∑' i, f n i) atTop (𝓝 (∑' i, g i)) :=
      tendsto_tsum_of_dominated_convergence hboundSum hpointwise
        (Eventually.of_forall hdom)
    have hgsum : (∑' i, g i) = if j = l then α j * c j ^ 2 else 0 := by
      by_cases hjl : j = l
      · subst l
        rw [tsum_eq_single (s j)]
        · simp [g, α, pow_two, mul_assoc]
        · intro i hi
          simp [g, hi]
      · have hsne : s j ≠ s l := fun h => hjl (hs h)
        have hgzero : g = 0 := by
          funext i
          by_cases hij : i = s j
          · subst i
            simp [g, hsne]
          · simp [g, hij]
        rw [hgzero]
        simp [hjl]
    have hre : Tendsto (fun n => (∑' i, f n i).re) atTop
        (𝓝 ((∑' i, g i).re)) :=
      Complex.continuous_re.continuousAt.tendsto.comp htsum
    have htwo := hre.const_mul 2
    rw [hgsum] at htwo
    by_cases hjl : j = l
    · subst l
      simpa [G, D, d, foldedTraceHankelGram, f] using htwo
    · simpa [G, D, d, foldedTraceHankelGram, f, hjl] using htwo
  have hDneg : ∀ x : Fin k → ℝ, x ≠ 0 → realQuad D x < 0 := by
    intro x hx
    apply realQuad_diagonal_neg d (fun j => by dsimp [d]; linarith [hc j]) x hx
  have hevent : ∀ᶠ n in atTop, ∀ x : Fin k → ℝ, x ≠ 0 → realQuad (G n) x < 0 :=
    eventually_realQuad_neg_of_entrywise_tendsto G D hDneg hconv
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨qn N, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro a ha j
    have hev := congrArg (fun p => evalRealPolynomial p (α j)) ha
    have hsumEval : evalRealPolynomial (∑ l, a l • qn N l) (α j) =
        ∑ l, (a l : ℂ) * evalRealPolynomial (qn N l) (α j) := by
      simp [evalRealPolynomial]
    rw [hsumEval] at hev
    have hcross (l : Fin k) (hl : l ≠ j) :
        evalRealPolynomial (qn N l) (α j) = 0 := by
      have hsne : s j ≠ s l := fun h => hl (hs h.symm)
      have hmemSelected : α j ∈ selected :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hmemF : α j ∈ F l := Finset.mem_union_right _ hmemSelected
      have hne' : α j ≠ α l := (horbit (s j) (s l) hsne).1
      have hconj' : α j ≠ (starRingEnd ℂ) (α l) :=
        (horbit (s j) (s l) hsne).2
      exact eval_phaseCorrectedSeparatorPolynomial_outer_zero hmemF hne' hconj' N
    have hsumSingle :
        (∑ l, (a l : ℂ) * evalRealPolynomial (qn N l) (α j)) =
          (a j : ℂ) * evalRealPolynomial (qn N j) (α j) := by
      refine Finset.sum_eq_single j ?_ ?_
      · intro l _hl hlj
        rw [hcross l hlj, mul_zero]
      · simp
    rw [hsumSingle, hevalTarget N j] at hev
    simp only [evalRealPolynomial_zero] at hev
    have haj : (a j : ℂ) = 0 := (mul_eq_zero.mp hev).resolve_right (hcne j)
    exact_mod_cast haj
  · intro x hx
    simpa [G] using hN N le_rfl x hx

theorem exists_foldedTraceHankelGram_negativePacket_of_upper
    {ι : Type*} (lam : ι → ℂ)
    (hne : ∀ i, lam i ≠ 0)
    (hfinite : ∀ {r : ℝ}, 0 < r → {i : ι | r ≤ ‖lam i‖}.Finite)
    (hsum : Summable lam)
    (hupper : ∀ i, 0 ≤ (lam i).im)
    {k : ℕ} (s : Fin k → ι)
    (hfold : Function.Injective (fun j => lam (s j)))
    (him : ∀ j, (lam (s j)).im ≠ 0) :
    ∃ q : Fin k → Polynomial ℝ,
      LinearIndependent ℝ q ∧
      ∀ x : Fin k → ℝ, x ≠ 0 →
        realQuad (fun j l => foldedTraceHankelGram lam (q j) (q l)) x < 0 := by
  classical
  let α : Fin k → ℂ := fun j => lam (s j)
  let c : Fin k → ℂ := fun j => Classical.choose (exists_phase_sq_re_neg (him j))
  have hc (j : Fin k) : (α j * c j ^ 2).re < 0 := by
    exact Classical.choose_spec (exists_phase_sq_re_neg (him j))
  have hcne (j : Fin k) : c j ≠ 0 := by
    intro hz
    have hcj := hc j
    rw [hz, zero_pow (by omega), mul_zero, Complex.zero_re] at hcj
    exact (lt_irrefl 0) hcj
  let outer : Fin k → Finset ι := fun j =>
    (hfinite (r := ‖α j‖) (norm_pos_iff.mpr (hne (s j)))).toFinset
  let selected : Finset ℂ := Finset.univ.image α
  let F : Fin k → Finset ℂ := fun j => (outer j).image lam ∪ selected
  let qn : ℕ → Fin k → Polynomial ℝ := fun n j =>
    phaseCorrectedSeparatorPolynomial (F j) (α j) (c j) n
  have hevalTarget (n : ℕ) (j : Fin k) :
      evalRealPolynomial (qn n j) (α j) = c j := by
    exact eval_phaseCorrectedSeparatorPolynomial_target (hne (s j)) (him j) n
  have hevalLimit (j : Fin k) (i : ι) :
      Tendsto (fun n => evalRealPolynomial (qn n j) (lam i)) atTop
        (𝓝 (if lam i = α j then c j else 0)) := by
    by_cases hiα : lam i = α j
    · simpa [hiα] using tendsto_const_nhds.congr' (Eventually.of_forall fun n =>
        show c j = evalRealPolynomial (qn n j) (lam i) by rw [hiα, hevalTarget])
    · have hic : lam i ≠ (starRingEnd ℂ) (α j) := by
        intro h
        have hu := hupper i
        rw [h, Complex.conj_im] at hu
        have hj := him j
        change (α j).im ≠ 0 at hj
        have hjpos : 0 < (α j).im := by
          exact lt_of_le_of_ne (hupper (s j)) (Ne.symm hj)
        linarith
      by_cases houter : ‖α j‖ ≤ ‖lam i‖
      · have hiOuter : i ∈ outer j := by
          simp only [outer, Set.Finite.mem_toFinset]
          exact houter
        have hiF : lam i ∈ F j := by
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiOuter, rfl⟩)
        have hzero (n : ℕ) : evalRealPolynomial (qn n j) (lam i) = 0 :=
          eval_phaseCorrectedSeparatorPolynomial_outer_zero hiF hiα hic n
        simpa [hiα] using tendsto_const_nhds.congr'
          (Eventually.of_forall fun n => (hzero n).symm)
      · have hinner : ‖lam i‖ < ‖α j‖ := lt_of_not_ge houter
        have ht := tendsto_eval_phaseCorrectedSeparatorPolynomial_zero
          (F := F j) (c := c j) (hne (s j)) (him j) hinner
        simpa [qn, hiα] using ht
  let C : Fin k → ℝ := fun j => phaseCorrectedSeparatorNormBound (F j) (α j) (c j)
  have hC (j : Fin k) : 0 ≤ C j :=
    phaseCorrectedSeparatorNormBound_nonneg (F j) (him j)
  have hevalBound (n : ℕ) (j : Fin k) (i : ι) :
      ‖evalRealPolynomial (qn n j) (lam i)‖ ≤ C j := by
    by_cases hle : ‖lam i‖ ≤ ‖α j‖
    · exact norm_eval_phaseCorrectedSeparatorPolynomial_le
        (F := F j) (c := c j) (hne (s j)) (him j) hle n
    · have houter : ‖α j‖ ≤ ‖lam i‖ := le_of_not_ge hle
      have hiOuter : i ∈ outer j := by
        simp only [outer, Set.Finite.mem_toFinset]
        exact houter
      have hiF : lam i ∈ F j :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hiOuter, rfl⟩)
      have hiα : lam i ≠ α j := by
        intro h
        apply hle
        rw [h]
      have hic : lam i ≠ (starRingEnd ℂ) (α j) := by
        intro h
        apply hle
        rw [h, norm_conj]
      rw [eval_phaseCorrectedSeparatorPolynomial_outer_zero hiF hiα hic n, norm_zero]
      exact hC j
  let G : ℕ → Matrix (Fin k) (Fin k) ℝ := fun n j l =>
    foldedTraceHankelGram lam (qn n j) (qn n l)
  let orbitPhase : Fin k → ι → ℂ := fun j i =>
    if lam i = α j then α j * c j ^ 2 else 0
  let d : Fin k → ℝ := fun j => 2 * (∑' i, orbitPhase j i).re
  let D : Matrix (Fin k) (Fin k) ℝ := Matrix.diagonal d
  have hconv (j l : Fin k) : Tendsto (fun n => G n j l) atTop (𝓝 (D j l)) := by
    let f : ℕ → ι → ℂ := fun n i =>
      lam i * evalRealPolynomial (qn n j) (lam i) *
        evalRealPolynomial (qn n l) (lam i)
    let g : ι → ℂ := fun i =>
      lam i * (if lam i = α j then c j else 0) *
        (if lam i = α l then c l else 0)
    have hpointwise (i : ι) : Tendsto (fun n => f n i) atTop (𝓝 (g i)) := by
      have hp := (hevalLimit j i).mul (hevalLimit l i)
      have hm := hp.const_mul (lam i)
      simpa only [f, g, mul_assoc] using hm
    let B : ℝ := C j * C l
    have hB : 0 ≤ B := mul_nonneg (hC j) (hC l)
    let bound : ι → ℝ := fun i => B * ‖lam i‖
    have hboundSum : Summable bound := hsum.norm.mul_left B
    have hdom : ∀ n i, ‖f n i‖ ≤ bound i := by
      intro n i
      calc
        ‖f n i‖ = ‖lam i‖ * ‖evalRealPolynomial (qn n j) (lam i)‖ *
            ‖evalRealPolynomial (qn n l) (lam i)‖ := by simp [f]
        _ ≤ ‖lam i‖ * C j * C l := by
          calc
            ‖lam i‖ * ‖evalRealPolynomial (qn n j) (lam i)‖ *
                ‖evalRealPolynomial (qn n l) (lam i)‖
                ≤ ‖lam i‖ * C j *
                    ‖evalRealPolynomial (qn n l) (lam i)‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left (hevalBound n j i) (norm_nonneg _))
                    (norm_nonneg _)
            _ ≤ ‖lam i‖ * C j * C l := by
                  exact mul_le_mul_of_nonneg_left (hevalBound n l i)
                    (mul_nonneg (norm_nonneg _) (hC j))
        _ = bound i := by simp [bound, B]; ring
    have htsum : Tendsto (fun n => ∑' i, f n i) atTop (𝓝 (∑' i, g i)) :=
      tendsto_tsum_of_dominated_convergence hboundSum hpointwise
        (Eventually.of_forall hdom)
    have hgsum : (∑' i, g i) = if j = l then ∑' i, orbitPhase j i else 0 := by
      by_cases hjl : j = l
      · subst l
        have hsame : g = orbitPhase j := by
          funext i
          by_cases hi : lam i = α j
          · simp [g, orbitPhase, hi, pow_two, mul_assoc]
          · simp [g, orbitPhase, hi]
        rw [hsame, if_pos rfl]
      · have hαne : α j ≠ α l := fun h => hjl (hfold h)
        have hgzero : g = 0 := by
          funext i
          by_cases hij : lam i = α j
          · have hil : lam i ≠ α l := fun h => hαne (hij.symm.trans h)
            simp [g, hij, hαne]
          · simp [g, hij]
        rw [hgzero]
        simp [hjl]
    have hre : Tendsto (fun n => (∑' i, f n i).re) atTop
        (𝓝 ((∑' i, g i).re)) :=
      Complex.continuous_re.continuousAt.tendsto.comp htsum
    have htwo := hre.const_mul 2
    rw [hgsum] at htwo
    by_cases hjl : j = l
    · subst l
      simpa [G, D, d, foldedTraceHankelGram, f] using htwo
    · simpa [G, D, d, foldedTraceHankelGram, f, hjl] using htwo
  have horbitPhaseNeg (j : Fin k) : (∑' i, orbitPhase j i).re < 0 := by
    let T : Finset ι := (outer j).filter (fun i => lam i = α j)
    have hsjT : s j ∈ T := by
      apply Finset.mem_filter.mpr
      constructor
      · simp only [outer, Set.Finite.mem_toFinset]
        change ‖α j‖ ≤ ‖lam (s j)‖
        exact le_rfl
      · rfl
    have hTnonempty : T.Nonempty := ⟨s j, hsjT⟩
    have houtside : ∀ i ∉ T, orbitPhase j i = 0 := by
      intro i hiT
      by_cases hi : lam i = α j
      · exfalso
        apply hiT
        apply Finset.mem_filter.mpr
        constructor
        · simp only [outer, Set.Finite.mem_toFinset]
          change ‖α j‖ ≤ ‖lam i‖
          rw [hi]
        · exact hi
      · simp [orbitPhase, hi]
    rw [tsum_eq_sum houtside, Complex.re_sum]
    apply Finset.sum_neg
    · intro i hiT
      have hi := (Finset.mem_filter.mp hiT).2
      simpa [orbitPhase, hi] using hc j
    · exact hTnonempty
  have hDneg : ∀ x : Fin k → ℝ, x ≠ 0 → realQuad D x < 0 := by
    intro x hx
    apply realQuad_diagonal_neg d (fun j => by dsimp [d]; linarith [horbitPhaseNeg j]) x hx
  have hevent : ∀ᶠ n in atTop, ∀ x : Fin k → ℝ, x ≠ 0 → realQuad (G n) x < 0 :=
    eventually_realQuad_neg_of_entrywise_tendsto G D hDneg hconv
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  refine ⟨qn N, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro a ha j
    have hev := congrArg (fun p => evalRealPolynomial p (α j)) ha
    have hsumEval : evalRealPolynomial (∑ l, a l • qn N l) (α j) =
        ∑ l, (a l : ℂ) * evalRealPolynomial (qn N l) (α j) := by
      simp [evalRealPolynomial]
    rw [hsumEval] at hev
    have hcross (l : Fin k) (hl : l ≠ j) :
        evalRealPolynomial (qn N l) (α j) = 0 := by
      have hmemSelected : α j ∈ selected :=
        Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
      have hmemF : α j ∈ F l := Finset.mem_union_right _ hmemSelected
      have hne' : α j ≠ α l := by
        intro h
        apply hl
        exact (hfold h).symm
      have hconj' : α j ≠ (starRingEnd ℂ) (α l) := by
        intro h
        have hu := hupper (s j)
        change 0 ≤ (α j).im at hu
        rw [h, Complex.conj_im] at hu
        have hil := him l
        change (α l).im ≠ 0 at hil
        have hilpos : 0 < (α l).im := by
          exact lt_of_le_of_ne (hupper (s l)) (Ne.symm hil)
        linarith
      exact eval_phaseCorrectedSeparatorPolynomial_outer_zero hmemF hne' hconj' N
    have hsumSingle :
        (∑ l, (a l : ℂ) * evalRealPolynomial (qn N l) (α j)) =
          (a j : ℂ) * evalRealPolynomial (qn N j) (α j) := by
      refine Finset.sum_eq_single j ?_ ?_
      · intro l _hl hlj
        rw [hcross l hlj, mul_zero]
      · simp
    rw [hsumSingle, hevalTarget N j] at hev
    simp only [evalRealPolynomial_zero] at hev
    have haj : (a j : ℂ) = 0 := (mul_eq_zero.mp hev).resolve_right (hcne j)
    exact_mod_cast haj
  · intro x hx
    simpa [G] using hN N le_rfl x hx

/-- With multiplicity fibers retained, the simultaneous block spans a real-polynomial subspace
of dimension `k`. -/
theorem exists_foldedTraceHankelPolynomialSubspace_negative_of_upper
    {ι : Type*} (lam : ι → ℂ)
    (hne : ∀ i, lam i ≠ 0)
    (hfinite : ∀ {r : ℝ}, 0 < r → {i : ι | r ≤ ‖lam i‖}.Finite)
    (hsum : Summable lam)
    (hupper : ∀ i, 0 ≤ (lam i).im)
    {k : ℕ} (s : Fin k → ι)
    (hfold : Function.Injective (fun j => lam (s j)))
    (him : ∀ j, (lam (s j)).im ≠ 0) :
    ∃ q : Fin k → Polynomial ℝ,
      Module.finrank ℝ (Submodule.span ℝ (Set.range q)) = k ∧
      ∀ x : Fin k → ℝ, x ≠ 0 →
        realQuad (fun j l => foldedTraceHankelGram lam (q j) (q l)) x < 0 := by
  obtain ⟨q, hq, hneg⟩ := exists_foldedTraceHankelGram_negativePacket_of_upper
    lam hne hfinite hsum hupper s hfold him
  refine ⟨q, ?_, hneg⟩
  rw [finrank_span_eq_card hq, Fintype.card_fin]

/-- The simultaneous block spans an actual real-polynomial subspace of dimension `k`. -/
theorem exists_foldedTraceHankelPolynomialSubspace_negative
    {ι : Type*} (lam : ι → ℂ)
    (hne : ∀ i, lam i ≠ 0)
    (hfinite : ∀ {r : ℝ}, 0 < r → {i : ι | r ≤ ‖lam i‖}.Finite)
    (hsum : Summable lam)
    (horbit : ∀ i j, i ≠ j →
      lam i ≠ lam j ∧ lam i ≠ (starRingEnd ℂ) (lam j))
    {k : ℕ} (s : Fin k → ι) (hs : Function.Injective s)
    (him : ∀ j, (lam (s j)).im ≠ 0) :
    ∃ q : Fin k → Polynomial ℝ,
      Module.finrank ℝ (Submodule.span ℝ (Set.range q)) = k ∧
      ∀ x : Fin k → ℝ, x ≠ 0 →
        realQuad (fun j l => foldedTraceHankelGram lam (q j) (q l)) x < 0 := by
  obtain ⟨q, hq, hneg⟩ := exists_foldedTraceHankelGram_negativePacket
    lam hne hfinite hsum horbit s hs him
  refine ⟨q, ?_, hneg⟩
  rw [finrank_span_eq_card hq, Fintype.card_fin]

end

end RHTower
