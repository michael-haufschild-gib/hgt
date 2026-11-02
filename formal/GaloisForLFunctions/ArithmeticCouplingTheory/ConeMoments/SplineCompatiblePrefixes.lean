import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineCorrectionSchedule

/-!
# Compatible prefixes with prescribed spline coefficients

Each new block changes only its heights. Exact finite interpolation cancels
all current cone moments, while exponential separation of real levels bounds
new residuals by the next block's correction radius.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

variable {a b d D : ℝ}

def PrescribedSplineSchedule.frequency (s : PrescribedSplineSchedule a b d D) (k : ℕ) : Finset ℝ :=
  coneSquare a b (quantitativeCutoff s.cutoff (s.start+k))

def PrescribedSplineSchedule.level (s : PrescribedSplineSchedule a b d D) (k : ℕ) : ℝ :=
  approachLevel d D (s.start+k)

def PrescribedSplineSchedule.point (s : PrescribedSplineSchedule a b d D)
    (γ : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (j : Fin (s.size k)) : ℂ :=
  (s.level k : ℂ)+(γ k j : ℂ)*Complex.I

lemma PrescribedSplineSchedule.point_re (s : PrescribedSplineSchedule a b d D)
    (γ : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (j : Fin (s.size k)) :
    (s.point γ k j).re=s.level k := by
  simp only [PrescribedSplineSchedule.point,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]

lemma PrescribedSplineSchedule.point_im (s : PrescribedSplineSchedule a b d D)
    (γ : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (j : Fin (s.size k)) :
    (s.point γ k j).im=γ k j := by
  simp only [PrescribedSplineSchedule.point,Complex.add_im,Complex.ofReal_re,Complex.mul_im,
    Complex.I_re,Complex.ofReal_im,Complex.I_im,mul_one,mul_zero,add_zero,zero_add]

def PrescribedSplineSchedule.blockMoment (s : PrescribedSplineSchedule a b d D)
    (γ : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  ∑ j, splineMomentCoefficient (s.point γ k j)*Complex.exp ((u : ℂ)*s.point γ k j)

def PrescribedSplineSchedule.prefixMoment (s : PrescribedSplineSchedule a b d D)
    (γ : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ range k, s.blockMoment γ j u

lemma PrescribedSplineSchedule.blockMoment_eq (s : PrescribedSplineSchedule a b d D)
    (γ : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (u : ℝ) :
    s.blockMoment γ k u=(Real.exp (s.level k*u) : ℂ)*
      ∑ j, splineMomentCoefficient (s.point γ k j)*phase u (γ k j) := by
  simp only [PrescribedSplineSchedule.blockMoment,PrescribedSplineSchedule.point,
    exp_level_eq,Finset.mul_sum]
  exact sum_congr rfl fun _ _ => by ring

lemma PrescribedSplineSchedule.block_norm_mass_le (s : PrescribedSplineSchedule a b d D)
    (hd : 0 < d) (hdD : d < D) {γ : (k : ℕ) → Fin (s.size k) → ℝ} {k : ℕ}
    (hγ : ∀ j, s.height k ≤ γ k j) :
    ∑ j, ‖splineMomentCoefficient (s.point γ k j)‖ ≤ (1/2 : ℝ)^k := by
  have hγ' : ∀ j, massRadius (2*correctionMass (s.start+k)) (s.size k) ≤ γ k j :=
    fun j => s.height_eq k ▸ hγ j
  have h := sum_norm_splineMomentCoefficient_le (δ := s.level k) (γ := γ k)
    (hd.le.trans (approachLevel_lower hdD (s.start+k))) (approachLevel_lt hdD (s.start+k)).le
    (correctionMass_pos (s.start+k)) (s.size_pos k)
    hγ'
  exact h.trans (s.mass_le k)

/-- A prefix contains only heights; every atom retains its exact spline coefficient. -/
structure SplinePrefix (s : PrescribedSplineSchedule a b d D) (k : ℕ) where
  height : (j : ℕ) → Fin (s.size j) → ℝ
  mem : ∀ j, j < k → ∀ l, height j l ∈ Set.Icc (s.height j) (s.height j+s.span j)
  injective : ∀ j, j < k → Function.Injective (height j)
  zero : ∀ l, l < k → ∀ u ∈ s.frequency l, s.prefixMoment height (l+1) u=0

def emptySplinePrefix (s : PrescribedSplineSchedule a b d D) : SplinePrefix s 0 where
  height := fun _ _ => 0
  mem := by intro j hj; omega
  injective := by intro j hj; omega
  zero := by intro j hj; omega

private lemma spline_half_mass_sum_le_two (k : ℕ) : ∑ j ∈ range k, (1/2 : ℝ)^j ≤ 2 := by
  have hs := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  have h := hs.summable.sum_le_tsum (range k) (fun j _ => by positivity)
  rw [hs.tsum_eq] at h
  norm_num at h
  exact h

lemma SplinePrefix.normalized_norm_le {s : PrescribedSplineSchedule a b d D} {k : ℕ}
    (c : SplinePrefix s (k+1)) (hd : 0 < d) (hdD : d < D) {u : ℝ} (hu : 0 ≤ u) :
    ‖(Real.exp (-s.level (k+1)*u) : ℂ)*s.prefixMoment c.height (k+1) u‖ ≤
      2*Real.exp (-(s.level (k+1)-s.level k)*u) := by
  have hblock : ∀ j ∈ range (k+1), ‖s.blockMoment c.height j u‖ ≤
      (1/2 : ℝ)^j*Real.exp (u*s.level k) := by
    intro j hj
    have hjk : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
    have hlevel : s.level j ≤ s.level k :=
      (strictMono_approachLevel hdD).monotone (Nat.add_le_add_left hjk s.start)
    have hexp : Real.exp (u*s.level j) ≤ Real.exp (u*s.level k) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlevel hu)
    have hm := s.block_norm_mass_le (γ := c.height) (k := j) hd hdD (fun l => (c.mem j (mem_range.mp hj) l).1)
    calc
      _ ≤ ∑ l, ‖splineMomentCoefficient (s.point c.height j l)*
          Complex.exp ((u : ℂ)*s.point c.height j l)‖ := norm_sum_le _ _
      _ = (∑ l, ‖splineMomentCoefficient (s.point c.height j l)‖)*Real.exp (u*s.level j) := by
        simp only [norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
          Complex.ofReal_im,zero_mul,sub_zero,s.point_re,Finset.sum_mul]
      _ ≤ (1/2 : ℝ)^j*Real.exp (u*s.level k) :=
        mul_le_mul hm hexp (Real.exp_pos _).le (by positivity)
  have hprefix : ‖s.prefixMoment c.height (k+1) u‖ ≤ 2*Real.exp (u*s.level k) := by
    calc
      _ ≤ ∑ j ∈ range (k+1), ‖s.blockMoment c.height j u‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range (k+1), (1/2 : ℝ)^j*Real.exp (u*s.level k) := sum_le_sum hblock
      _ = (∑ j ∈ range (k+1), (1/2 : ℝ)^j)*Real.exp (u*s.level k) := (sum_mul _ _ _).symm
      _ ≤ 2*Real.exp (u*s.level k) :=
        mul_le_mul_of_nonneg_right (spline_half_mass_sum_le_two _) (Real.exp_pos _).le
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-s.level (k+1)*u)*(2*Real.exp (u*s.level k)) :=
      mul_le_mul_of_nonneg_left hprefix (Real.exp_pos _).le
    _ = _ := by rw [mul_left_comm,← Real.exp_add]; congr 2; ring

lemma SplinePrefix.residual_small {s : PrescribedSplineSchedule a b d D} {k : ℕ}
    (c : SplinePrefix s k) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d < D)
    {u : ℝ} (hu : u ∈ s.frequency k) :
    ‖(Real.exp (-s.level k*u) : ℂ)*s.prefixMoment c.height k u‖ ≤
      2*(correctionMass (s.start+k))^2 := by
  classical
  cases k with
  | zero =>
    simp only [PrescribedSplineSchedule.prefixMoment,range_zero,sum_empty,mul_zero,norm_zero]
    positivity
  | succ k =>
    by_cases huk : u ∈ s.frequency k
    · rw [c.zero k (Nat.lt_succ_self k) u huk,mul_zero,norm_zero]
      positivity
    · have hnew : u ∈ coneSquare a b (quantitativeCutoff s.cutoff (s.start+k+1)) \
          coneSquare a b (quantitativeCutoff s.cutoff (s.start+k)) := by
        exact mem_sdiff.mpr ⟨by simpa only [PrescribedSplineSchedule.frequency,Nat.add_assoc] using hu,huk⟩
      have htail := cone_new_frequency_squared_mass_bound ha hb hdD s.cutoff_tail (s.start+k) hnew
      have hnorm := c.normalized_norm_le hd hdD (coneSquare_positive ha hb hu).le
      exact hnorm.trans (by simpa only [PrescribedSplineSchedule.level,Nat.add_assoc] using htail)


/-- The next correction changes only the new block's heights. -/
lemma exists_splinePrefix_extension {s : PrescribedSplineSchedule a b d D} {k : ℕ}
    (c : SplinePrefix s k) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d < D) :
    ∃ c' : SplinePrefix s (k+1), ∀ j, j < k → c'.height j=c.height j := by
  classical
  let r : s.frequency k → ℂ := fun u =>
    -((Real.exp (-s.level k*u.val) : ℂ)*s.prefixMoment c.height k u.val)
  have hr : ∀ u, ‖r u‖ ≤ 2*(correctionMass (s.start+k))^2 := by
    intro u
    change ‖-((Real.exp (-s.level k*u.val) : ℂ)*s.prefixMoment c.height k u.val)‖ ≤ _
    rw [norm_neg]
    exact c.residual_small ha hb hd hdD u.property
  obtain ⟨v,hvinj,hvmem,hvmoment⟩ := s.correct k r hr
  let γ : (j : ℕ) → Fin (s.size j) → ℝ := Function.update c.height k v
  have hγk : γ k=v := Function.update_self _ _ _
  have hγo : ∀ j, j ≠ k → γ j=c.height j := fun j hj => Function.update_of_ne hj _ _
  have hprefix : ∀ l, l ≤ k → ∀ u, s.prefixMoment γ l u=s.prefixMoment c.height l u := by
    intro l hl u
    apply sum_congr rfl
    intro j hj
    have hjk : j ≠ k := by have := mem_range.mp hj; omega
    simp only [PrescribedSplineSchedule.blockMoment,PrescribedSplineSchedule.point,hγo j hjk]
  have hnew : ∀ u ∈ s.frequency k, s.prefixMoment γ (k+1) u=0 := by
    intro u hu
    have he : s.prefixMoment γ (k+1) u=s.prefixMoment c.height k u+
        (Real.exp (s.level k*u) : ℂ)*
          ∑ j, splineMomentCoefficient ((s.level k : ℂ)+(v j : ℂ)*Complex.I)*phase u (v j) := by
      rw [PrescribedSplineSchedule.prefixMoment,sum_range_succ]
      change s.prefixMoment γ k u+s.blockMoment γ k u= _
      rw [hprefix k le_rfl,s.blockMoment_eq]
      simp only [PrescribedSplineSchedule.point,hγk]
    have hvu := hvmoment ⟨u,hu⟩
    change (∑ j, splineMomentCoefficient ((s.level k : ℂ)+(v j : ℂ)*Complex.I)*phase u (v j))=
      r ⟨u,hu⟩ at hvu
    rw [he,hvu]
    change s.prefixMoment c.height k u+(Real.exp (s.level k*u) : ℂ)*
      (-((Real.exp (-s.level k*u) : ℂ)*s.prefixMoment c.height k u))=0
    have hcancel : (Real.exp (s.level k*u) : ℂ)*(Real.exp (-s.level k*u) : ℂ)=1 := by
      rw [← Complex.ofReal_mul,← Real.exp_add]
      simp only [neg_mul,add_neg_cancel,Real.exp_zero,Complex.ofReal_one]
    rw [mul_neg,← mul_assoc,hcancel,one_mul,add_neg_cancel]
  let c' : SplinePrefix s (k+1) := {
    height := γ
    mem := by
      intro j hj l
      by_cases hjk : j=k
      · subst j
        rw [hγk]
        exact hvmem l
      · rw [hγo j hjk]
        exact c.mem j (by omega) l
    injective := by
      intro j hj
      by_cases hjk : j=k
      · subst j
        rw [hγk]
        exact hvinj
      · rw [hγo j hjk]
        exact c.injective j (by omega)
    zero := by
      intro l hl u hu
      by_cases hlk : l=k
      · subst l
        exact hnew u hu
      · rw [hprefix (l+1) (by omega)]
        exact c.zero l (by omega) u hu
  }
  exact ⟨c',fun j hj => hγo j (by omega)⟩

/-- All finite prefix moments vanish with exact spline coefficients and distinct
heights in each prescribed block. -/
theorem exists_spline_prefix_heights (s : PrescribedSplineSchedule a b d D)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d < D) :
    ∃ γ : (k : ℕ) → Fin (s.size k) → ℝ,
      (∀ k j, γ k j ∈ Set.Icc (s.height k) (s.height k+s.span k)) ∧
      (∀ k, Function.Injective (γ k)) ∧
      (∀ k u, u ∈ s.frequency k → s.prefixMoment γ (k+1) u=0) := by
  classical
  let next : (k : ℕ) → SplinePrefix s k → SplinePrefix s (k+1) :=
    fun _ c => (exists_splinePrefix_extension c ha hb hd hdD).choose
  have hnext : ∀ k (c : SplinePrefix s k) j, j < k → (next k c).height j=c.height j :=
    fun _ c => (exists_splinePrefix_extension c ha hb hd hdD).choose_spec
  let stages : (k : ℕ) → SplinePrefix s k := Nat.rec (emptySplinePrefix s) next
  have hstep : ∀ k j, j < k → (stages (k+1)).height j=(stages k).height j :=
    fun k j hj => hnext k (stages k) j hj
  let γ : (k : ℕ) → Fin (s.size k) → ℝ := fun k => (stages (k+1)).height k
  have hstable : ∀ k j, j < k → (stages k).height j=γ j := by
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      intro j hj
      by_cases hjk : j < k
      · rw [hstep k j hjk,ih j hjk]
      · have he : j=k := by omega
        subst j
        rfl
  refine ⟨γ,?_,?_,?_⟩
  · intro k j
    exact (stages (k+1)).mem k (Nat.lt_succ_self k) j
  · intro k
    exact (stages (k+1)).injective k (Nat.lt_succ_self k)
  · intro k u hu
    calc
      s.prefixMoment γ (k+1) u=s.prefixMoment (stages (k+1)).height (k+1) u := by
        apply sum_congr rfl
        intro j hj
        simp only [PrescribedSplineSchedule.blockMoment,PrescribedSplineSchedule.point,
          hstable (k+1) j (mem_range.mp hj)]
      _ = 0 := (stages (k+1)).zero k (Nat.lt_succ_self k) u hu

#print axioms SplinePrefix.residual_small
#print axioms exists_spline_prefix_heights
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
