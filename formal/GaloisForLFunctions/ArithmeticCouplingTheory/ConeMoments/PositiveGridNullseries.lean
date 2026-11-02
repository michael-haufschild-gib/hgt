import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.QuantitativeConeCutoffs

/-!
# Positive grid nullseries

An exhaustive positive-correction schedule admits weights on any prescribed
translations of its grids. Each finite prefix cancels its frequency window;
later blocks individually cancel every earlier window. Summable block masses
therefore give absolutely convergent zero moments at every cone time.

The atomic rank is injective and bounded by the cumulative node count, which
allows height placement to enforce local finiteness without changing moments.
-/

open Finset Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

def PositiveGridSchedule.point {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (k : ℕ) (j : Fin (s.size k)) : ℂ :=
  (approachLevel d D k : ℂ)+((H k+j.val*(Real.pi/(2*s.radius k)) : ℝ) : ℂ)*Complex.I

def PositiveGridSchedule.blockMoment {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (w : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  finiteLaplaceSum (s.point H k) (w k) u

def PositiveGridSchedule.prefixMoment {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (w : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (u : ℝ) : ℂ :=
  ∑ j ∈ range k, s.blockMoment H w j u

lemma PositiveGridSchedule.point_re {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (k : ℕ) (j : Fin (s.size k)) : (s.point H k j).re=approachLevel d D k := by
  simp only [PositiveGridSchedule.point, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

/-- A finite prefix records exact masses, positive weight bounds, and all earlier cancelled moments. -/
structure GridPrefix {a b d D : ℝ} (s : PositiveGridSchedule a b d D) (H : ℕ → ℝ) (k : ℕ) where
  weight : (j : ℕ) → Fin (s.size j) → ℝ
  bounds : ∀ j, j < k → ∀ l, 0 < weight j l ∧ correctionMass j/(2*s.size j) ≤ weight j l ∧
    weight j l ≤ 3*correctionMass j/(2*s.size j)
  mass : ∀ j, j < k → ∑ l, weight j l=correctionMass j
  zero : ∀ l, l < k → ∀ u ∈ s.frequency l, s.prefixMoment H weight (l+1) u=0

def emptyGridPrefix {a b d D : ℝ} (s : PositiveGridSchedule a b d D) (H : ℕ → ℝ) :
    GridPrefix s H 0 where
  weight := fun _ _ => 0
  bounds := by intro j hj; omega
  mass := by intro j hj; omega
  zero := by intro j hj; omega

/-- At the next real level, the old prefix is controlled only by its total mass and real width. -/
lemma GridPrefix.normalized_norm_le {a b d D : ℝ} {s : PositiveGridSchedule a b d D}
    {H : ℕ → ℝ} {k : ℕ} (c : GridPrefix s H (k+1)) (hdD : d < D) {u : ℝ} (hu : 0 ≤ u) :
    ‖(Real.exp (-approachLevel d D (k+1)*u) : ℂ)*s.prefixMoment H c.weight (k+1) u‖ ≤
      2*Real.exp (-(approachLevel d D (k+1)-approachLevel d D k)*u) := by
  have hblock : ∀ j ∈ range (k+1), ‖s.blockMoment H c.weight j u‖ ≤
      correctionMass j*Real.exp (u*approachLevel d D k) := by
    intro j hj
    have hjk : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
    have h := finiteLaplaceSum_norm_le (d := approachLevel d D k) (s.point H j) (c.weight j)
      (fun l => (c.bounds j (mem_range.mp hj) l).1.le)
      (fun l => by rw [s.point_re]; exact (strictMono_approachLevel hdD).monotone hjk) hu
    rw [c.mass j (mem_range.mp hj)] at h
    exact h
  have hmass : ∑ j ∈ range (k+1), correctionMass j ≤ 2 :=
    (correctionMass_summable.sum_le_tsum (range (k+1)) (fun j _ => (correctionMass_pos j).le)).trans
      correctionMass_tsum_le_two
  have hprefix : ‖s.prefixMoment H c.weight (k+1) u‖ ≤ 2*Real.exp (u*approachLevel d D k) := by
    calc
      _ ≤ ∑ j ∈ range (k+1), ‖s.blockMoment H c.weight j u‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range (k+1), correctionMass j*Real.exp (u*approachLevel d D k) := sum_le_sum hblock
      _ = (∑ j ∈ range (k+1), correctionMass j)*Real.exp (u*approachLevel d D k) := (sum_mul _ _ _).symm
      _ ≤ 2*Real.exp (u*approachLevel d D k) := mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (-approachLevel d D (k+1)*u)*(2*Real.exp (u*approachLevel d D k)) :=
      mul_le_mul_of_nonneg_left hprefix (Real.exp_pos _).le
    _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- Already cancelled frequencies vanish from the normalized residual budget. -/
lemma GridPrefix.residual_small {a b d D : ℝ} {s : PositiveGridSchedule a b d D}
    {H : ℕ → ℝ} {k : ℕ} (c : GridPrefix s H k) (hdD : d < D) :
    (∑ u ∈ s.frequency k,
      ‖(Real.exp (-approachLevel d D k*u) : ℂ)*s.prefixMoment H c.weight k u‖) ≤ correctionMass k/16 := by
  classical
  cases k with
  | zero =>
    simp only [PositiveGridSchedule.prefixMoment, range_zero, sum_empty, mul_zero,
      norm_zero, sum_const_zero]
    exact div_nonneg (correctionMass_pos 0).le (by norm_num)
  | succ k =>
    have he : (∑ u ∈ s.frequency (k+1),
        ‖(Real.exp (-approachLevel d D (k+1)*u) : ℂ)*s.prefixMoment H c.weight (k+1) u‖) =
        ∑ u ∈ s.frequency (k+1) \ s.frequency k,
        ‖(Real.exp (-approachLevel d D (k+1)*u) : ℂ)*s.prefixMoment H c.weight (k+1) u‖ := by
      symm
      apply sum_subset sdiff_subset
      intro u hu hnot
      have huk : u ∈ s.frequency k := by
        by_contra h
        exact hnot (mem_sdiff.mpr ⟨hu, h⟩)
      rw [c.zero k (Nat.lt_succ_self k) u huk, mul_zero, norm_zero]
    rw [he]
    calc
      _ ≤ ∑ u ∈ s.frequency (k+1) \ s.frequency k,
          2*Real.exp (-(approachLevel d D (k+1)-approachLevel d D k)*u) := by
        apply sum_le_sum
        intro u hu
        exact c.normalized_norm_le hdD (s.positive (k+1) u (mem_sdiff.mp hu).1).le
      _ = 2*∑ u ∈ s.frequency (k+1) \ s.frequency k,
          Real.exp (-(approachLevel d D (k+1)-approachLevel d D k)*u) := (mul_sum _ _ _).symm
      _ ≤ correctionMass (k+1)/16 := s.tail k

lemma PositiveGridSchedule.blockMoment_eq {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (w : (k : ℕ) → Fin (s.size k) → ℝ) (k : ℕ) (u : ℝ) :
    s.blockMoment H w k u=(Real.exp (approachLevel d D k*u) : ℂ)*
      ∑ j, (w k j : ℂ)*phase u (H k+j.val*(Real.pi/(2*s.radius k))) := by
  simp only [PositiveGridSchedule.blockMoment, finiteLaplaceSum, PositiveGridSchedule.point,
    exp_level_eq, Finset.mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- One positive correction extends the prefix without changing any earlier weight. -/
lemma exists_gridPrefix_extension {a b d D : ℝ} {s : PositiveGridSchedule a b d D}
    {H : ℕ → ℝ} {k : ℕ} (c : GridPrefix s H k) (hdD : d < D) :
    ∃ c' : GridPrefix s H (k+1), ∀ j, j < k → c'.weight j=c.weight j := by
  classical
  let r : ℝ → ℂ := fun u => (Real.exp (-approachLevel d D k*u) : ℂ)*s.prefixMoment H c.weight k u
  obtain ⟨v, hv, hmass, hmoment⟩ := s.correct k (correctionMass k) (correctionMass_pos k)
    r (c.residual_small hdD) (H k)
  let w : (j : ℕ) → Fin (s.size j) → ℝ := Function.update c.weight k v
  have hwk : w k=v := Function.update_self _ _ _
  have hwo : ∀ j, j ≠ k → w j=c.weight j := fun j hj => Function.update_of_ne hj _ _
  have hprefix : ∀ l, l ≤ k → ∀ u, s.prefixMoment H w l u=s.prefixMoment H c.weight l u := by
    intro l hl u
    apply sum_congr rfl
    intro j hj
    have hjk : j ≠ k := by have := mem_range.mp hj; omega
    simp only [PositiveGridSchedule.blockMoment, hwo j hjk]
  have hnew : ∀ u ∈ s.frequency k, s.prefixMoment H w (k+1) u=0 := by
    intro u hu
    have he : s.prefixMoment H w (k+1) u = s.prefixMoment H c.weight k u+
        (Real.exp (approachLevel d D k*u) : ℂ)*
          ∑ j, (v j : ℂ)*phase u (H k+j.val*(Real.pi/(2*s.radius k))) := by
      rw [PositiveGridSchedule.prefixMoment, sum_range_succ]
      change s.prefixMoment H w k u+s.blockMoment H w k u= _
      rw [hprefix k le_rfl, s.blockMoment_eq, hwk]
    rw [he, hmoment u hu]
    change s.prefixMoment H c.weight k u+
      (Real.exp (approachLevel d D k*u) : ℂ)*
      (-((Real.exp (-approachLevel d D k*u) : ℂ)*s.prefixMoment H c.weight k u))=0
    have hcancel : (Real.exp (approachLevel d D k*u) : ℂ)*
        (Real.exp (-approachLevel d D k*u) : ℂ)=1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      simp only [neg_mul, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    rw [mul_neg, ← mul_assoc, hcancel, one_mul, add_neg_cancel]
  let c' : GridPrefix s H (k+1) := {
    weight := w
    bounds := by
      intro j hj l
      by_cases hjk : j=k
      · subst j
        rw [hwk]
        exact hv l
      · rw [hwo j hjk]
        exact c.bounds j (by omega) l
    mass := by
      intro j hj
      by_cases hjk : j=k
      · subst j
        rw [hwk]
        exact hmass
      · rw [hwo j hjk]
        exact c.mass j (by omega)
    zero := by
      intro l hl u hu
      by_cases hlk : l=k
      · subst l
        exact hnew u hu
      · rw [hprefix (l+1) (by omega)]
        exact c.zero l (by omega) u hu
  }
  exact ⟨c', fun j hj => hwo j (by omega)⟩

/-- Any prescribed translations admit positive block weights whose finite prefixes
cancel their exhaustive windows exactly. -/
theorem exists_grid_weights {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (hdD : d < D) (H : ℕ → ℝ) :
    ∃ w : (k : ℕ) → Fin (s.size k) → ℝ,
      (∀ k j, 0 < w k j ∧ correctionMass k/(2*s.size k) ≤ w k j ∧
        w k j ≤ 3*correctionMass k/(2*s.size k)) ∧
      (∀ k, ∑ j, w k j=correctionMass k) ∧
      (∀ k u, u ∈ s.frequency k → s.prefixMoment H w (k+1) u=0) := by
  classical
  let next : (k : ℕ) → GridPrefix s H k → GridPrefix s H (k+1) :=
    fun k c => (exists_gridPrefix_extension c hdD).choose
  have hnext : ∀ k (c : GridPrefix s H k) j, j < k → (next k c).weight j=c.weight j :=
    fun k c => (exists_gridPrefix_extension c hdD).choose_spec
  let stages : (k : ℕ) → GridPrefix s H k := Nat.rec (emptyGridPrefix s H) next
  have hstep : ∀ k j, j < k → (stages (k+1)).weight j=(stages k).weight j :=
    fun k j hj => hnext k (stages k) j hj
  let w : (k : ℕ) → Fin (s.size k) → ℝ := fun k => (stages (k+1)).weight k
  have hstable : ∀ k j, j < k → (stages k).weight j=w j := by
    intro k
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      intro j hj
      by_cases hjk : j < k
      · rw [hstep k j hjk, ih j hjk]
      · have he : j=k := by omega
        subst j
        rfl
  refine ⟨w, ?_, ?_, ?_⟩
  · intro k j
    exact (stages (k+1)).bounds k (Nat.lt_succ_self k) j
  · intro k
    exact (stages (k+1)).mass k (Nat.lt_succ_self k)
  · intro k u hu
    calc
      s.prefixMoment H w (k+1) u = s.prefixMoment H (stages (k+1)).weight (k+1) u := by
        apply sum_congr rfl
        intro j hj
        simp only [PositiveGridSchedule.blockMoment, hstable (k+1) j (mem_range.mp hj)]
      _ = 0 := (stages (k+1)).zero k (Nat.lt_succ_self k) u hu

abbrev PositiveGridSchedule.AtomIndex {a b d D : ℝ} (s : PositiveGridSchedule a b d D) :=
  (k : ℕ) × Fin (s.size k)

def PositiveGridSchedule.atom {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (i : s.AtomIndex) : ℂ := s.point H i.1 i.2

def PositiveGridSchedule.atomWeight {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (w : (k : ℕ) → Fin (s.size k) → ℝ) (i : s.AtomIndex) : ℝ := w i.1 i.2

lemma summable_grid_weight {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (w : (k : ℕ) → Fin (s.size k) → ℝ) (hw : ∀ k j, 0 ≤ w k j)
    (hmass : ∀ k, ∑ j, w k j=correctionMass k) : Summable (s.atomWeight w) := by
  rw [summable_sigma_of_nonneg (f := s.atomWeight w) (fun i => hw i.1 i.2)]
  refine ⟨fun _ => Summable.of_finite, ?_⟩
  have he : (fun k => ∑' j : Fin (s.size k), s.atomWeight w ⟨k,j⟩)=correctionMass := by
    funext k
    rw [tsum_fintype]
    exact hmass k
  rw [he]
  exact correctionMass_summable

lemma hasSum_grid_weight {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (w : (k : ℕ) → Fin (s.size k) → ℝ) (hw : ∀ k j, 0 ≤ w k j)
    (hmass : ∀ k, ∑ j, w k j=correctionMass k) :
    HasSum (s.atomWeight w) (∑' k, correctionMass k) := by
  have hs := summable_grid_weight s w hw hmass
  have hσ := hs.hasSum.sigma (fun k => hasSum_fintype
    (fun j : Fin (s.size k) => s.atomWeight w ⟨k,j⟩))
  change HasSum (fun k => ∑ j, w k j) (∑' i, s.atomWeight w i) at hσ
  simp_rw [hmass] at hσ
  rw [← hσ.unique correctionMass_summable.hasSum]
  exact hs.hasSum

lemma summable_grid_moment {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (w : (k : ℕ) → Fin (s.size k) → ℝ)
    (hd : 0 < d) (hdD : d < D) (hw : ∀ k j, 0 < w k j)
    (hmass : ∀ k, ∑ j, w k j=correctionMass k) (u : ℝ) :
    Summable (fun i : s.AtomIndex => (s.atomWeight w i : ℂ)*Complex.exp ((u : ℂ)*s.atom H i)) := by
  have hs := summable_grid_weight s w (fun k j => (hw k j).le) hmass
  refine Summable.of_norm_bounded (hs.mul_right (Real.exp (|u| * D))) fun i => ?_
  dsimp only [PositiveGridSchedule.atomWeight]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hw i.1 i.2), Complex.norm_exp]
  have he : ((u : ℂ)*s.atom H i).re=u*approachLevel d D i.1 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      PositiveGridSchedule.atom, s.point_re]
  rw [he]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hw i.1 i.2).le
  exact (mul_le_mul_of_nonneg_right (le_abs_self u) (hd.le.trans (approachLevel_lower hdD i.1))).trans
    (mul_le_mul_of_nonneg_left (approachLevel_lt hdD i.1).le (abs_nonneg u))

lemma hasSum_grid_block_moment {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (w : (k : ℕ) → Fin (s.size k) → ℝ)
    (hz : ∀ k u, u ∈ s.frequency k → s.prefixMoment H w (k+1) u=0)
    {N : ℕ} {u : ℝ} (hu : u ∈ s.frequency N) :
    HasSum (fun k => s.blockMoment H w k u) 0 := by
  have hp : ∀ k, N ≤ k → s.prefixMoment H w (k+1) u=0 :=
    fun k hk => hz k u (s.nested N k hk hu)
  have hzero : ∀ k ∉ range (N+1), s.blockMoment H w k u=0 := by
    intro k hk
    rw [mem_range, not_lt] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k=j+1 := ⟨k-1, by omega⟩
    have h := hp (j+1) (by omega)
    rw [PositiveGridSchedule.prefixMoment, sum_range_succ] at h
    change s.prefixMoment H w (j+1) u+s.blockMoment H w (j+1) u=0 at h
    rwa [hp j (by omega), zero_add] at h
  have h : HasSum (fun k => s.blockMoment H w k u)
      (∑ k ∈ range (N+1), s.blockMoment H w k u) := hasSum_sum_of_ne_finset_zero hzero
  change HasSum (fun k => s.blockMoment H w k u) (s.prefixMoment H w (N+1) u) at h
  rwa [hp N le_rfl] at h

/-- Exhausted samples have absolutely convergent zero moments on the atomic support. -/
theorem hasSum_grid_atomic_moment {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (w : (k : ℕ) → Fin (s.size k) → ℝ)
    (hd : 0 < d) (hdD : d < D) (hw : ∀ k j, 0 < w k j)
    (hmass : ∀ k, ∑ j, w k j=correctionMass k)
    (hz : ∀ k u, u ∈ s.frequency k → s.prefixMoment H w (k+1) u=0)
    (t : PositiveCone a b) :
    HasSum (fun i : s.AtomIndex => (s.atomWeight w i : ℂ)*Complex.exp ((t.val : ℂ)*s.atom H i)) 0 := by
  obtain ⟨N, hN⟩ := s.covers t
  have hs := summable_grid_moment s H w hd hdD hw hmass t.val
  have hσ := hs.hasSum.sigma (fun k => hasSum_fintype
    (fun j : Fin (s.size k) => (w k j : ℂ)*Complex.exp ((t.val : ℂ)*s.point H k j)))
  change HasSum (fun k => s.blockMoment H w k t.val)
    (∑' i : s.AtomIndex, (s.atomWeight w i : ℂ)*Complex.exp ((t.val : ℂ)*s.atom H i)) at hσ
  rw [← hσ.unique (hasSum_grid_block_moment s H w hz hN)]
  exact hs.hasSum

lemma PositiveGridSchedule.point_im {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (H : ℕ → ℝ) (k : ℕ) (j : Fin (s.size k)) :
    (s.point H k j).im=H k+j.val*(Real.pi/(2*s.radius k)) := by
  simp only [PositiveGridSchedule.point, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]

def PositiveGridSchedule.atomOffset {a b d D : ℝ} (s : PositiveGridSchedule a b d D) (k : ℕ) : ℕ :=
  ∑ j ∈ range k, s.size j

def PositiveGridSchedule.atomRank {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (i : s.AtomIndex) : ℕ := s.atomOffset i.1+i.2.val

lemma PositiveGridSchedule.atomOffset_mono {a b d D : ℝ} (s : PositiveGridSchedule a b d D) :
    Monotone s.atomOffset := by
  apply monotone_nat_of_le_succ
  intro k
  change (∑ j ∈ range k, s.size j) ≤ ∑ j ∈ range (k+1), s.size j
  rw [sum_range_succ]
  exact Nat.le_add_right _ _

lemma PositiveGridSchedule.atomRank_lt_prefix {a b d D : ℝ} (s : PositiveGridSchedule a b d D)
    (i : s.AtomIndex) : s.atomRank i < gridPrefixSize s.size i.1 := by
  rw [PositiveGridSchedule.atomRank, PositiveGridSchedule.atomOffset, gridPrefixSize, sum_range_succ]
  exact Nat.add_lt_add_left i.2.isLt _

lemma PositiveGridSchedule.atomRank_injective {a b d D : ℝ} (s : PositiveGridSchedule a b d D) :
    Function.Injective s.atomRank := by
  have hlt : ∀ i j : s.AtomIndex, i.1 < j.1 → s.atomRank i < s.atomRank j := by
    intro i j hij
    have h := s.atomOffset_mono (Nat.succ_le_of_lt hij)
    rw [PositiveGridSchedule.atomOffset, sum_range_succ] at h
    have hi := i.2.isLt
    change (∑ k ∈ range i.1, s.size k)+s.size i.1 ≤ s.atomOffset j.1 at h
    dsimp only [PositiveGridSchedule.atomRank, PositiveGridSchedule.atomOffset]
    dsimp only [PositiveGridSchedule.atomOffset] at h
    omega
  intro i j hij
  have hfst : i.1=j.1 := by
    rcases lt_trichotomy i.1 j.1 with h | h | h
    · exact False.elim ((ne_of_lt (hlt i j h)) hij)
    · exact h
    · exact False.elim ((ne_of_lt (hlt j i h)) hij.symm)
  rcases i with ⟨k,i⟩
  rcases j with ⟨l,j⟩
  dsimp only at hfst
  subst l
  have hval : i.val=j.val := Nat.add_left_cancel hij
  exact congrArg (fun t : Fin (s.size k) => (⟨k,t⟩ : s.AtomIndex)) (Fin.ext hval)

#print axioms exists_grid_weights
#print axioms hasSum_grid_atomic_moment
#print axioms PositiveGridSchedule.atomRank_injective
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
