import GaloisForLFunctions.HTGeometry.FiniteMonotonicityVariation
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Topology.DiscreteSubset

/-!
# From absent critical points to a monotonicity cell

A continuous nonvanishing function on a closed interval has constant sign: taking both signs would
force a zero by the intermediate value theorem.  Applied to the derivative, a cell free of critical
points is a monotonicity cell.

This is the bridge between the Sturm cell count -- which says each one-sign cell contains at most
one critical point -- and the finite-monotonicity variation law, whose hypothesis is a partition
into monotonicity intervals.
-/

open Set

namespace HTGeometry

/-- **A continuous nonvanishing function on an interval has constant sign.** -/
theorem sign_const_of_continuousOn_ne_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) (hne : ∀ x ∈ Icc a b, g x ≠ 0) :
    (∀ x ∈ Icc a b, 0 < g x) ∨ (∀ x ∈ Icc a b, g x < 0) := by
  have hmemA : a ∈ Icc a b := ⟨le_refl a, hab⟩
  rcases lt_or_gt_of_ne (hne a hmemA) with hneg | hpos
  · refine Or.inr fun x hx => ?_
    by_contra hcon
    push Not at hcon
    have hx0 : 0 < g x := lt_of_le_of_ne hcon (Ne.symm (hne x hx))
    have hax : a ≤ x := hx.1
    have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc (le_refl a) hx.2
    have hzero : (0 : ℝ) ∈ g '' Icc a x :=
      intermediate_value_Icc hax (hg.mono hsub) ⟨hneg.le, hx0.le⟩
    obtain ⟨c, hc, hgc⟩ := hzero
    exact hne c (hsub hc) hgc
  · refine Or.inl fun x hx => ?_
    by_contra hcon
    push Not at hcon
    have hx0 : g x < 0 := lt_of_le_of_ne hcon (hne x hx)
    have hax : a ≤ x := hx.1
    have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc (le_refl a) hx.2
    have hzero : (0 : ℝ) ∈ g '' Icc a x :=
      intermediate_value_Icc' hax (hg.mono hsub) ⟨hx0.le, hpos.le⟩
    obtain ⟨c, hc, hgc⟩ := hzero
    exact hne c (hsub hc) hgc

/-- **A cell without critical points is a monotonicity cell.** -/
theorem monotoneOn_or_antitoneOn_of_deriv_ne_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : ContinuousOn (deriv f) (Icc a b))
    (hne : ∀ x ∈ Icc a b, deriv f x ≠ 0) :
    MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b) := by
  rcases sign_const_of_continuousOn_ne_zero hab hd hne with hpos | hneg
  · refine Or.inl (strictMonoOn_of_deriv_pos (convex_Icc a b) hc ?_).monotoneOn
    intro x hx
    exact hpos x (interior_subset hx)
  · refine Or.inr (strictAntiOn_of_deriv_neg (convex_Icc a b) hc ?_).antitoneOn
    intro x hx
    exact hneg x (interior_subset hx)

/-- **Variation bound from a critical-point-free partition.**  An ordered partition whose cells
carry no critical point is a monotonicity partition, so the finite-monotonicity law applies. -/
theorem eVariationOn_le_of_no_critical_points (f : ℝ → ℝ) (I : ℕ → ℝ) (n : ℕ) (hI : Monotone I)
    (hc : ∀ i < n, ContinuousOn f (Icc (I i) (I (i + 1))))
    (hd : ∀ i < n, ContinuousOn (deriv f) (Icc (I i) (I (i + 1))))
    (hne : ∀ i < n, ∀ x ∈ Icc (I i) (I (i + 1)), deriv f x ≠ 0)
    (B : ℝ) (hbound : ∀ x ∈ Icc (I 0) (I n), |f x| ≤ B) :
    eVariationOn f (Icc (I 0) (I n)) ≤ ENNReal.ofReal (2 * n * B) :=
  eVariationOn_le_of_piecewise_monotone f I n hI
    (fun i hi => monotoneOn_or_antitoneOn_of_deriv_ne_zero (hI (Nat.le_succ i)) (hc i hi)
      (hd i hi) (hne i hi)) B hbound

/-! ### The open-cell form

A partition by critical points has vanishing derivative *at* the partition points, so the usable
hypothesis is nonvanishing on the open cell only.  Monotonicity needs no more than that, since
`strictMonoOn_of_deriv_pos` already asks for positivity on the interior. -/

/-- **Constant sign on an open interval.** -/
theorem sign_const_of_continuousOn_ne_zero_Ioo {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Ioo a b)) (hne : ∀ x ∈ Ioo a b, g x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < g x) ∨ (∀ x ∈ Ioo a b, g x < 0) := by
  rcases (Ioo a b).eq_empty_or_nonempty with hempty | ⟨c, hc⟩
  · refine Or.inl fun x hx => ?_
    rw [hempty] at hx
    exact absurd hx (Set.notMem_empty x)
  · have hsub : ∀ x ∈ Ioo a b, Set.uIcc c x ⊆ Ioo a b := fun x hx =>
      (Set.ordConnected_Ioo).uIcc_subset hc hx
    rcases lt_or_gt_of_ne (hne c hc) with hneg | hpos
    · refine Or.inr fun x hx => ?_
      by_contra hcon
      push Not at hcon
      have hx0 : 0 < g x := lt_of_le_of_ne hcon (Ne.symm (hne x hx))
      have hzero : (0 : ℝ) ∈ g '' Set.uIcc c x :=
        intermediate_value_uIcc (hg.mono (hsub x hx))
          (Set.mem_uIcc_of_le hneg.le hx0.le)
      obtain ⟨z, hz, hgz⟩ := hzero
      exact hne z (hsub x hx hz) hgz
    · refine Or.inl fun x hx => ?_
      by_contra hcon
      push Not at hcon
      have hx0 : g x < 0 := lt_of_le_of_ne hcon (hne x hx)
      have hzero : (0 : ℝ) ∈ g '' Set.uIcc c x :=
        intermediate_value_uIcc (hg.mono (hsub x hx))
          (Set.mem_uIcc_of_ge hx0.le hpos.le)
      obtain ⟨z, hz, hgz⟩ := hzero
      exact hne z (hsub x hx hz) hgz

/-- **A cell whose interior carries no critical point is a monotonicity cell.** -/
theorem monotoneOn_or_antitoneOn_of_deriv_ne_zero_Ioo {f : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hd : ContinuousOn (deriv f) (Ioo a b))
    (hne : ∀ x ∈ Ioo a b, deriv f x ≠ 0) :
    MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b) := by
  rcases sign_const_of_continuousOn_ne_zero_Ioo hd hne with hpos | hneg
  · refine Or.inl (strictMonoOn_of_deriv_pos (convex_Icc a b) hc ?_).monotoneOn
    intro x hx
    rw [interior_Icc] at hx
    exact hpos x hx
  · refine Or.inr (strictAntiOn_of_deriv_neg (convex_Icc a b) hc ?_).antitoneOn
    intro x hx
    rw [interior_Icc] at hx
    exact hneg x hx

/-- **Variation bound from a partition whose open cells are critical-point free.**  This is the
form the Sturm cell count supplies: critical points are allowed at the partition points themselves,
which is exactly where they sit. -/
theorem eVariationOn_le_of_no_interior_critical_points (f : ℝ → ℝ) (I : ℕ → ℝ) (n : ℕ)
    (hI : Monotone I) (hc : ∀ i < n, ContinuousOn f (Icc (I i) (I (i + 1))))
    (hd : ∀ i < n, ContinuousOn (deriv f) (Ioo (I i) (I (i + 1))))
    (hne : ∀ i < n, ∀ x ∈ Ioo (I i) (I (i + 1)), deriv f x ≠ 0)
    (B : ℝ) (hbound : ∀ x ∈ Icc (I 0) (I n), |f x| ≤ B) :
    eVariationOn f (Icc (I 0) (I n)) ≤ ENNReal.ofReal (2 * n * B) :=
  eVariationOn_le_of_piecewise_monotone f I n hI
    (fun i hi => monotoneOn_or_antitoneOn_of_deriv_ne_zero_Ioo (hc i hi) (hd i hi) (hne i hi))
    B hbound

/-! ### Assembling the ordered partition -/

/-- **From a finite critical set to an ordered partition.**  Sorting the critical points together
with the endpoints gives a monotone partition of `[a,b]` whose open cells contain no critical
point. -/
theorem exists_partition_of_finite_critical {a b : ℝ} (hab : a ≤ b) (S : Finset ℝ)
    (hS : ∀ x ∈ S, x ∈ Ioo a b) :
    ∃ (n : ℕ) (I : ℕ → ℝ), n ≤ S.card + 1 ∧ Monotone I ∧ I 0 = a ∧ I n = b ∧
      ∀ i, i < n → ∀ x ∈ Ioo (I i) (I (i + 1)), x ∉ S := by
  classical
  set T : Finset ℝ := insert a (insert b S) with hT
  have haT : a ∈ T := Finset.mem_insert_self _ _
  have hbT : b ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hbounds : ∀ x ∈ T, a ≤ x ∧ x ≤ b := by
    intro x hx
    rw [hT, Finset.mem_insert, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨le_refl _, hab⟩
    · exact ⟨hab, le_refl _⟩
    · exact ⟨(hS x hx).1.le, (hS x hx).2.le⟩
  set m : ℕ := T.card with hm
  have hmpos : 0 < m := Finset.card_pos.mpr ⟨a, haT⟩
  set e := T.orderIsoOfFin (rfl : T.card = m) with he
  set I : ℕ → ℝ := fun i => if h : i < m then (e ⟨i, h⟩ : ℝ) else b with hI
  have hImem : ∀ i (h : i < m), I i = (e ⟨i, h⟩ : ℝ) := by
    intro i h
    simp only [hI]
    rw [dif_pos h]
  have hIout : ∀ i, ¬ i < m → I i = b := by
    intro i h
    simp only [hI]
    rw [dif_neg h]
  have hImemT : ∀ i (h : i < m), I i ∈ T := by
    intro i h
    rw [hImem i h]
    exact (e ⟨i, h⟩).2
  have hIle : ∀ i, I i ≤ b := by
    intro i
    by_cases h : i < m
    · exact (hbounds _ (hImemT i h)).2
    · rw [hIout i h]
  have hIcmp : ∀ i j (hi : i < m) (hj : j < m), i ≤ j → I i ≤ I j := by
    intro i j hi hj hij
    rw [hImem i hi, hImem j hj]
    have : (⟨i, hi⟩ : Fin m) ≤ ⟨j, hj⟩ := by rw [Fin.le_def]; exact hij
    exact_mod_cast e.monotone this
  have hmono : Monotone I := by
    intro i j hij
    by_cases hj : j < m
    · exact hIcmp i j (lt_of_le_of_lt hij hj) hj hij
    · rw [hIout j hj]
      exact hIle i
  have hkey : ∀ (x : ℝ) (hx : x ∈ T), ∃ k, k < m ∧ I k = x := by
    intro x hx
    obtain ⟨k, hk⟩ := e.surjective ⟨x, hx⟩
    refine ⟨k.val, k.isLt, ?_⟩
    rw [hImem k.val k.isLt]
    have : (⟨k.val, k.isLt⟩ : Fin m) = k := rfl
    rw [this, hk]
  have hzero : I 0 = a := by
    refine le_antisymm ?_ (hbounds _ (hImemT 0 hmpos)).1
    obtain ⟨k, hk, hka⟩ := hkey a haT
    rw [← hka]
    exact hIcmp 0 k hmpos hk (Nat.zero_le k)
  have hlt : m - 1 < m := by omega
  have hlast : I (m - 1) = b := by
    refine le_antisymm (hbounds _ (hImemT (m - 1) hlt)).2 ?_
    obtain ⟨k, hk, hkb⟩ := hkey b hbT
    rw [← hkb]
    exact hIcmp k (m - 1) hk hlt (by omega)
  have hcard : m ≤ S.card + 2 := by
    have h1 : T.card ≤ (insert b S).card + 1 := Finset.card_insert_le _ _
    have h2 : (insert b S).card ≤ S.card + 1 := Finset.card_insert_le _ _
    omega
  refine ⟨m - 1, I, by omega, hmono, hzero, hlast, ?_⟩
  intro i hi x hx hxS
  have hi1 : i + 1 < m := by omega
  have hi0 : i < m := by omega
  have hxT : x ∈ T := by
    rw [hT]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxS)
  obtain ⟨k, hk, hkx⟩ := hkey x hxT
  have h1 : i < k := by
    by_contra hcon
    have : I k ≤ I i := hIcmp k i hk hi0 (by omega)
    rw [hkx] at this
    exact absurd hx.1 (not_lt.mpr this)
  have h2 : k < i + 1 := by
    by_contra hcon
    have : I (i + 1) ≤ I k := hIcmp (i + 1) k hi1 hk (by omega)
    rw [hkx] at this
    exact absurd hx.2 (not_lt.mpr this)
  omega

/-- **Bounded variation from a finite critical set.**  A bounded function whose critical points in
the open interval are finitely many has total variation at most `2 (|S| + 1) B`.  This is the
abstract form of the one-turning-point argument: the differential equation supplies the finite
critical set, the uniform bound supplies `B`. -/
theorem eVariationOn_le_of_finite_critical {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn (deriv f) (Icc a b))
    (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Ioo a b)
    (hcrit : ∀ x ∈ Ioo a b, deriv f x = 0 → x ∈ S)
    (B : ℝ) (hbound : ∀ x ∈ Icc a b, |f x| ≤ B) :
    ∃ n : ℕ, n ≤ S.card + 1 ∧
      eVariationOn f (Icc a b) ≤ ENNReal.ofReal (2 * n * B) := by
  obtain ⟨n, I, hn, hmono, hzero, hlast, hcell⟩ := exists_partition_of_finite_critical hab S hS
  refine ⟨n, hn, ?_⟩
  have hIa : ∀ i, i ≤ n → a ≤ I i := fun i hi => hzero ▸ hmono (Nat.zero_le i)
  have hIb : ∀ i, i ≤ n → I i ≤ b := fun i hi => hlast ▸ hmono hi
  have hcellsub : ∀ i, i < n → Icc (I i) (I (i + 1)) ⊆ Icc a b := by
    intro i hi
    exact Icc_subset_Icc (hIa i (le_of_lt hi)) (hIb (i + 1) hi)
  have hcellsubOpen : ∀ i, i < n → Ioo (I i) (I (i + 1)) ⊆ Ioo a b := by
    intro i hi x hx
    exact ⟨lt_of_le_of_lt (hIa i (le_of_lt hi)) hx.1,
      lt_of_lt_of_le hx.2 (hIb (i + 1) hi)⟩
  have hres := eVariationOn_le_of_no_interior_critical_points f I n hmono
    (fun i hi => hcf.mono (hcellsub i hi))
    (fun i hi => hdf.mono ((hcellsubOpen i hi).trans Ioo_subset_Icc_self))
    (fun i hi x hx hzero' => hcell i hi x hx (hcrit x (hcellsubOpen i hi hx) hzero'))
    B (by rw [hzero, hlast]; exact hbound)
  rw [hzero, hlast] at hres
  exact hres

/-- **Finiteness corollary.**  A bounded function with finitely many critical points is of bounded
variation, which is the hypothesis the BV lattice-envelope modules consume. -/
theorem boundedVariationOn_of_finite_critical {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn (deriv f) (Icc a b))
    (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Ioo a b)
    (hcrit : ∀ x ∈ Ioo a b, deriv f x = 0 → x ∈ S)
    (B : ℝ) (hbound : ∀ x ∈ Icc a b, |f x| ≤ B) :
    BoundedVariationOn f (Icc a b) := by
  obtain ⟨n, _, hle⟩ :=
    eVariationOn_le_of_finite_critical hab hcf hdf S hS hcrit B hbound
  exact ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)

/-! ### Finiteness of the critical set from a one-sign cell decomposition -/

/-- **A finite decomposition into cells with at most one critical point each has a finite critical
set.**  This is the reduction of the nodal count: the classical input is only that the Sturm
right-hand side changes sign finitely often. -/
theorem finite_criticalSet_of_cells {f : ℝ → ℝ} {J : ℕ → ℝ} (hJ : Monotone J) :
    ∀ N : ℕ, (∀ k, k < N → {x | x ∈ Icc (J k) (J (k + 1)) ∧ deriv f x = 0}.Subsingleton) →
      {x | x ∈ Icc (J 0) (J N) ∧ deriv f x = 0}.Finite := by
  intro N
  induction N with
  | zero =>
      intro _
      refine Set.Finite.subset (Set.finite_singleton (J 0)) ?_
      rintro x ⟨hx, -⟩
      rw [Icc_self] at hx
      exact hx
  | succ N ih =>
      intro hcell
      have hsplit : Icc (J 0) (J (N + 1)) = Icc (J 0) (J N) ∪ Icc (J N) (J (N + 1)) :=
        (Icc_union_Icc_eq_Icc (hJ (Nat.zero_le N)) (hJ (Nat.le_succ N))).symm
      have h1 := ih fun k hk => hcell k (by omega)
      have h2 : {x | x ∈ Icc (J N) (J (N + 1)) ∧ deriv f x = 0}.Finite :=
        (hcell N (by omega)).finite
      refine Set.Finite.subset (h1.union h2) ?_
      rintro x ⟨hx, hd⟩
      rw [hsplit] at hx
      rcases hx with hx | hx
      · exact Or.inl ⟨hx, hd⟩
      · exact Or.inr ⟨hx, hd⟩

/-- **Bounded variation from a finite critical set, stated for a set rather than a finset.** -/
theorem boundedVariationOn_of_finite_criticalSet {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn (deriv f) (Icc a b))
    (hfin : {x | x ∈ Ioo a b ∧ deriv f x = 0}.Finite)
    (B : ℝ) (hbound : ∀ x ∈ Icc a b, |f x| ≤ B) :
    BoundedVariationOn f (Icc a b) := by
  classical
  refine boundedVariationOn_of_finite_critical hab hcf hdf hfin.toFinset ?_ ?_ B hbound
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact hx.1
  · intro x hx hzero
    rw [Set.Finite.mem_toFinset]
    exact ⟨hx, hzero⟩

/-! ### From finitely many sign changes to bounded variation -/

/-- **Finitely many zeros of the Sturm right-hand side give a finite critical set.**  The zero set
partitions the interval; on each open cell the right-hand side has constant sign, so the one-sign
Sturm law leaves at most one critical point per cell. -/
theorem finite_criticalSet_of_finite_rhs_zeros {p q f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hflux : ContinuousOn (sturmFlux p f) (Icc a b))
    (hode : ∀ x ∈ Ioo a b, deriv (sturmFlux p f) x = q x * f x)
    (hrhsc : ContinuousOn (fun x => q x * f x) (Icc a b))
    (Z : Finset ℝ) (hZ : ∀ x ∈ Z, x ∈ Ioo a b)
    (hzero : ∀ x ∈ Ioo a b, q x * f x = 0 → x ∈ Z) :
    {x | x ∈ Icc a b ∧ deriv f x = 0}.Finite := by
  obtain ⟨N, J, -, hJ, hJ0, hJN, hcellZ⟩ := exists_partition_of_finite_critical hab Z hZ
  have hJa : ∀ i, a ≤ J i := fun i => hJ0 ▸ hJ (Nat.zero_le i)
  have hJb : ∀ i, i ≤ N → J i ≤ b := fun i hi => hJN ▸ hJ hi
  have hres : {x | x ∈ Icc (J 0) (J N) ∧ deriv f x = 0}.Finite := by
    refine finite_criticalSet_of_cells hJ N fun k hk => ?_
    have hsub : Icc (J k) (J (k + 1)) ⊆ Icc a b :=
      Icc_subset_Icc (hJa k) (hJb (k + 1) hk)
    have hsubO : Ioo (J k) (J (k + 1)) ⊆ Ioo a b := fun x hx =>
      ⟨lt_of_le_of_lt (hJa k) hx.1, lt_of_lt_of_le hx.2 (hJb (k + 1) hk)⟩
    have hne : ∀ x ∈ Ioo (J k) (J (k + 1)), q x * f x ≠ 0 := by
      intro x hx hz
      exact hcellZ k hk x hx (hzero x (hsubO hx) hz)
    rcases sign_const_of_continuousOn_ne_zero_Ioo
      (hrhsc.mono (Ioo_subset_Icc_self.trans hsub)) hne with hpos | hneg
    · exact criticalSet_subsingleton_of_sturm_rhs_pos p q f (hflux.mono hsub)
        (fun x hx => hode x (hsubO hx)) hpos
    · exact criticalSet_subsingleton_of_sturm_rhs_neg p q f (hflux.mono hsub)
        (fun x hx => hode x (hsubO hx)) hneg
  rw [hJ0, hJN] at hres
  exact hres

/-- **Bounded variation of a Sturm solution from finitely many right-hand-side zeros.**  The whole
one-turning-point argument, with the classical input reduced to a sign-change count. -/
theorem boundedVariationOn_of_finite_rhs_zeros {p q f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn (deriv f) (Icc a b))
    (hflux : ContinuousOn (sturmFlux p f) (Icc a b))
    (hode : ∀ x ∈ Ioo a b, deriv (sturmFlux p f) x = q x * f x)
    (hrhsc : ContinuousOn (fun x => q x * f x) (Icc a b))
    (Z : Finset ℝ) (hZ : ∀ x ∈ Z, x ∈ Ioo a b)
    (hzero : ∀ x ∈ Ioo a b, q x * f x = 0 → x ∈ Z)
    (B : ℝ) (hbound : ∀ x ∈ Icc a b, |f x| ≤ B) :
    BoundedVariationOn f (Icc a b) := by
  refine boundedVariationOn_of_finite_criticalSet hab hcf hdf ?_ B hbound
  refine Set.Finite.subset
    (finite_criticalSet_of_finite_rhs_zeros hab hflux hode hrhsc Z hZ hzero) ?_
  rintro x ⟨hx, hd⟩
  exact ⟨Ioo_subset_Icc_self hx, hd⟩

/-! ### Finiteness of a zero set -/

/-- **Zeros with nonvanishing derivative are finitely many on a compact interval.**  Each such zero
is isolated, and a discrete compact set is finite.  For a Sturm solution the hypothesis is exactly
nontriviality: a common zero of the solution and its derivative would make it vanish identically. -/
theorem finite_zeros_of_deriv_ne_zero {f : ℝ → ℝ} {a b : ℝ}
    (hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hne : ∀ x ∈ Icc a b, f x = 0 → deriv f x ≠ 0) :
    {x | x ∈ Icc a b ∧ f x = 0}.Finite := by
  have hcont : ContinuousOn f (Icc a b) := fun x hx =>
    ((hdiff x hx).continuousAt).continuousWithinAt
  have hEq : {x | x ∈ Icc a b ∧ f x = 0} = Icc a b ∩ f ⁻¹' {0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
  have hclosed : IsClosed (Icc a b ∩ f ⁻¹' {0}) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact {x | x ∈ Icc a b ∧ f x = 0} := by
    rw [hEq]
    exact isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  refine hcompact.finite ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [Filter.inf_principal_eq_bot]
  have hd : HasDerivAt f (deriv f x) x := (hdiff x hx.1).hasDerivAt
  have htend : Filter.Tendsto f (nhdsWithin x {x}ᶜ) (nhdsWithin (f x) {f x}ᶜ) :=
    HasDerivAt.tendsto_nhdsNE hd (hne x hx.1 hx.2)
  have hev := htend (self_mem_nhdsWithin (a := f x) (s := ({f x}ᶜ : Set ℝ)))
  refine Filter.mem_of_superset hev ?_
  intro y hy hyZ
  exact hy (by rw [hyZ.2, hx.2]; exact rfl)

/-- The zero set of a product is the union of the two zero sets. -/
theorem finite_zeros_mul {q f : ℝ → ℝ} {a b : ℝ}
    (hq : {x | x ∈ Icc a b ∧ q x = 0}.Finite) (hf : {x | x ∈ Icc a b ∧ f x = 0}.Finite) :
    {x | x ∈ Icc a b ∧ q x * f x = 0}.Finite := by
  refine Set.Finite.subset (hq.union hf) ?_
  rintro x ⟨hx, hmul⟩
  rcases mul_eq_zero.mp hmul with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

/-! ### Interface to a second-order equation

The variation chain consumes the Sturm form `deriv (sturmFlux p f) x = q x * f x`.  A concrete
second-order equation supplies it through the derivative of `y -> p y * deriv f y`, which is the
Sturm flux by definition. -/

theorem deriv_sturmFlux_eq_of_hasDerivAt {p q f : ℝ → ℝ} {x : ℝ}
    (h : HasDerivAt (fun y => p y * deriv f y) (q x * f x) x) :
    deriv (sturmFlux p f) x = q x * f x := h.deriv

theorem ode_of_hasDerivAt_on {p q f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ x ∈ Ioo a b, HasDerivAt (fun y => p y * deriv f y) (q x * f x) x) :
    ∀ x ∈ Ioo a b, deriv (sturmFlux p f) x = q x * f x :=
  fun x hx => deriv_sturmFlux_eq_of_hasDerivAt (h x hx)

/-- **The one-turning-point law from a second-order equation.**  Everything the concrete instance
must supply: the second-order equation in flux form, continuity of the flux and of the right-hand
side, finitely many right-hand-side zeros, and a uniform bound. -/
theorem boundedVariationOn_of_secondOrder {p q f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn (deriv f) (Icc a b))
    (hflux : ContinuousOn (sturmFlux p f) (Icc a b))
    (hode : ∀ x ∈ Ioo a b, HasDerivAt (fun y => p y * deriv f y) (q x * f x) x)
    (hrhsc : ContinuousOn (fun x => q x * f x) (Icc a b))
    (Z : Finset ℝ) (hZ : ∀ x ∈ Z, x ∈ Ioo a b)
    (hzero : ∀ x ∈ Ioo a b, q x * f x = 0 → x ∈ Z)
    (B : ℝ) (hbound : ∀ x ∈ Icc a b, |f x| ≤ B) :
    BoundedVariationOn f (Icc a b) :=
  boundedVariationOn_of_finite_rhs_zeros hab hcf hdf hflux (ode_of_hasDerivAt_on hode) hrhsc
    Z hZ hzero B hbound

end HTGeometry
