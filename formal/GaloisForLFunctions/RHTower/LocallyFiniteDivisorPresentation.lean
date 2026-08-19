import GaloisForLFunctions.RHTower.AnderssonDivisorAtOrigin

/-!
# Presenting a locally finite divisor by zero and pole sequences

A signed divisor on the plane whose support meets every ball in a finite set is the divisor of a
quotient of Weierstrass products times a power of `z`.  The presentation is by two sequences: the
support away from the origin is enumerated shell by shell with multiplicity, and both sequences are
completed by one and the same auxiliary sequence, so the completion cancels in the divisor.
-/

noncomputable section

open Filter Set Complex GaloisForLFunctions.HTGeometry

namespace RHTower

/-- A divisor is locally finite when every ball meets its support in a finite set. -/
def LocallyFiniteDivisor (D : ℂ → ℤ) : Prop := ∀ R : ℝ, {z : ℂ | D z ≠ 0 ∧ ‖z‖ ≤ R}.Finite

/-- The `k`-th shell of the support of a divisor. -/
def divisorShell (D : ℂ → ℤ) (k : ℕ) : Set ℂ :=
  {z : ℂ | D z ≠ 0 ∧ (k : ℝ) < ‖z‖ ∧ ‖z‖ ≤ (k : ℝ) + 1}

theorem finite_divisorShell {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (k : ℕ) :
    (divisorShell D k).Finite :=
  (hlf ((k : ℝ) + 1)).subset fun _ hz => ⟨hz.1, hz.2.2⟩

/-- The points of a shell, listed without repetition. -/
def shellList (D : ℂ → ℤ) (hlf : LocallyFiniteDivisor D) (k : ℕ) : List ℂ :=
  (finite_divisorShell hlf k).toFinset.toList

theorem shellList_nodup {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (k : ℕ) :
    (shellList D hlf k).Nodup := Finset.nodup_toList _

theorem mem_shellList {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (k : ℕ) (z : ℂ) :
    z ∈ shellList D hlf k ↔ z ∈ divisorShell D k := by
  rw [shellList, Finset.mem_toList, Set.Finite.mem_toFinset]

/-- The `j`-th point of the `k`-th shell. -/
def shellPoint (D : ℂ → ℤ) (hlf : LocallyFiniteDivisor D) (k j : ℕ) : ℂ :=
  (shellList D hlf k).getD j 0

theorem shellPoint_mem {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) {k j : ℕ}
    (hj : j < (shellList D hlf k).length) : shellPoint D hlf k j ∈ divisorShell D k := by
  rw [shellPoint, List.getD_eq_getElem _ _ hj]
  exact (mem_shellList hlf k _).1 (List.getElem_mem hj)

/-- Every support point away from the origin sits in exactly one shell, at exactly one index. -/
theorem exists_unique_shell {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) {z : ℂ} (hz : D z ≠ 0)
    (hz0 : z ≠ 0) :
    ∃! p : ℕ × ℕ, p.2 < (shellList D hlf p.1).length ∧ shellPoint D hlf p.1 p.2 = z := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set k : ℕ := ⌈‖z‖⌉₊ - 1 with hkdef
  have hceil : 0 < ⌈‖z‖⌉₊ := Nat.ceil_pos.2 hnorm
  have hk1 : (k : ℝ) + 1 = (⌈‖z‖⌉₊ : ℝ) := by
    rw [hkdef]
    have : (1:ℕ) ≤ ⌈‖z‖⌉₊ := hceil
    push_cast [Nat.cast_sub this]
    ring
  have hmemshell : z ∈ divisorShell D k := by
    refine ⟨hz, ?_, ?_⟩
    · have hlt : (⌈‖z‖⌉₊ : ℝ) - 1 < ‖z‖ := by
        have := Nat.ceil_lt_add_one (le_of_lt hnorm)
        linarith
      have : (k : ℝ) = (⌈‖z‖⌉₊ : ℝ) - 1 := by linarith [hk1]
      rw [this]
      exact hlt
    · rw [hk1]
      exact Nat.le_ceil _
  have hmemlist : z ∈ shellList D hlf k := (mem_shellList hlf k z).2 hmemshell
  obtain ⟨j, hj, hjz⟩ : ∃ j, ∃ h : j < (shellList D hlf k).length,
      (shellList D hlf k)[j] = z := List.getElem_of_mem hmemlist
  refine ⟨(k, j), ⟨hj, by rw [shellPoint, List.getD_eq_getElem _ _ hj]; exact hjz⟩, ?_⟩
  rintro ⟨k', j'⟩ ⟨hj', hval⟩
  have hmem' : z ∈ divisorShell D k' := by
    rw [← hval]
    exact shellPoint_mem hlf hj'
  have hkk : k' = k := by
    have h1 : (k' : ℝ) < ‖z‖ := hmem'.2.1
    have h2 : ‖z‖ ≤ (k' : ℝ) + 1 := hmem'.2.2
    have h3 : (k : ℝ) < ‖z‖ := hmemshell.2.1
    have h4 : ‖z‖ ≤ (k : ℝ) + 1 := hmemshell.2.2
    have hA : (k' : ℝ) < (k : ℝ) + 1 := by linarith
    have hB : (k : ℝ) < (k' : ℝ) + 1 := by linarith
    have hA' : k' < k + 1 := by exact_mod_cast hA
    have hB' : k < k' + 1 := by exact_mod_cast hB
    omega
  subst hkk
  have hjj : j' = j := by
    have hjz' : (shellList D hlf k)[j'] = z := by
      rw [← hval, shellPoint, List.getD_eq_getElem _ _ hj']
    have hinj := (shellList_nodup hlf k).getElem_inj_iff (i := j') (hi := hj') (j := j) (hj := hj)
    exact hinj.1 (by rw [hjz', hjz])
  rw [hjj]

attribute [local instance] Classical.propDecidable

/-- The auxiliary points completing both sequences. -/
def padPoint (i : ℕ) : ℂ := (-((i : ℝ) + 1) : ℝ)

theorem norm_padPoint (i : ℕ) : ‖padPoint i‖ = (i : ℝ) + 1 := by
  have hi : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  rw [padPoint, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  ring

theorem padPoint_ne_zero (i : ℕ) : padPoint i ≠ 0 := by
  intro h
  have hn := norm_padPoint i
  rw [h, norm_zero] at hn
  have hi : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

theorem re_padPoint_lt_one (i : ℕ) : (padPoint i).re < 1 := by
  rw [padPoint, Complex.ofReal_re]
  have : (0:ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

theorem padPoint_injective : Function.Injective padPoint := by
  intro i j h
  have hi := norm_padPoint i
  have hj := norm_padPoint j
  rw [h, hj] at hi
  exact_mod_cast (by linarith : (i : ℝ) = (j : ℝ))

/-- The occupied slots of a sequence enumerating a multiplicity function. -/
def slot (D : ℂ → ℤ) (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ) (n : ℕ) : Prop :=
  n.unpair.2.unpair.1 < (shellList D hlf n.unpair.1).length ∧
    n.unpair.2.unpair.2 < mult (shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1)

/-- The sequence enumerating a multiplicity function, completed by the auxiliary points. -/
def divisorSeq (D : ℂ → ℤ) (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ) : ℕ → ℂ := fun n =>
  if slot D hlf mult n then shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1
  else padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n)

theorem infinite_compl_slot (D : ℂ → ℤ) (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ) :
    {n : ℕ | ¬ slot D hlf mult n}.Infinite := by
  set L : ℕ := (shellList D hlf 0).length with hLdef
  refine Set.infinite_of_injective_forall_mem
    (f := fun i : ℕ => Nat.pair 0 (Nat.pair (L + i) 0)) ?_ ?_
  · intro i j hij
    have h1 : Nat.pair (L + i) 0 = Nat.pair (L + j) 0 := by
      have := congrArg Nat.unpair hij
      simpa using this
    have h2 : L + i = L + j := by
      have := congrArg Nat.unpair h1
      simpa using this
    omega
  · intro i
    simp only [Set.mem_setOf_eq, slot, Nat.unpair_pair]
    intro hcon
    have := hcon.1
    omega

theorem divisorSeq_ne_zero {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ) (n : ℕ) :
    divisorSeq D hlf mult n ≠ 0 := by
  rw [divisorSeq]
  by_cases h : slot D hlf mult n
  · rw [if_pos h]
    have hmem := shellPoint_mem hlf h.1
    intro h0
    have hnorm := hmem.2.1
    rw [h0, norm_zero] at hnorm
    have hk : (0:ℝ) ≤ ((n.unpair.1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  · rw [if_neg h]
    exact padPoint_ne_zero _

theorem re_divisorSeq_lt_one {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D)
    (hsupp : ∀ z : ℂ, D z ≠ 0 → z.re < 1) (mult : ℂ → ℕ) (n : ℕ) :
    (divisorSeq D hlf mult n).re < 1 := by
  rw [divisorSeq]
  by_cases h : slot D hlf mult n
  · rw [if_pos h]
    exact hsupp _ (shellPoint_mem hlf h.1).1
  · rw [if_neg h]
    exact re_padPoint_lt_one _

theorem slot_fiber_eq {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ) {z : ℂ}
    {k₀ j₀ : ℕ}
    (huniq : ∀ p : ℕ × ℕ,
      (p.2 < (shellList D hlf p.1).length ∧ shellPoint D hlf p.1 p.2 = z) → p = (k₀, j₀))
    (hj₀ : j₀ < (shellList D hlf k₀).length) (hval₀ : shellPoint D hlf k₀ j₀ = z) :
    {n : ℕ | slot D hlf mult n ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z}
      = (fun m : ℕ => Nat.pair k₀ (Nat.pair j₀ m)) '' (↑(Finset.range (mult z)) : Set ℕ) := by
  classical
  ext n
  constructor
  · rintro ⟨hslot, hvalue⟩
    have hpair : (n.unpair.1, n.unpair.2.unpair.1) = (k₀, j₀) := huniq _ ⟨hslot.1, hvalue⟩
    have hk : n.unpair.1 = k₀ := congrArg Prod.fst hpair
    have hj : n.unpair.2.unpair.1 = j₀ := congrArg Prod.snd hpair
    refine ⟨n.unpair.2.unpair.2, ?_, ?_⟩
    · have hm := hslot.2
      rw [hvalue] at hm
      simpa using hm
    · show Nat.pair k₀ (Nat.pair j₀ n.unpair.2.unpair.2) = n
      rw [← hk, ← hj, Nat.pair_unpair, Nat.pair_unpair]
  · rintro ⟨m, hm, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio] at hm
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp only [Nat.unpair_pair]
    · exact hj₀
    · rw [hval₀]
      exact hm
    · exact hval₀

theorem ncard_slot_fiber {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ)
    (hmultsupp : ∀ z, mult z ≠ 0 → D z ≠ 0) {z : ℂ} (hz0 : z ≠ 0) :
    {n : ℕ | slot D hlf mult n ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z}.ncard
      = mult z := by
  classical
  by_cases hmz : mult z = 0
  · have hempty : {n : ℕ | slot D hlf mult n
        ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hslot, hvalue⟩
      have hm := hslot.2
      rw [hvalue, hmz] at hm
      omega
    rw [hempty, Set.ncard_empty, hmz]
  · obtain ⟨⟨k₀, j₀⟩, ⟨hj₀, hval₀⟩, huniq⟩ := exists_unique_shell hlf (hmultsupp z hmz) hz0
    rw [slot_fiber_eq hlf mult huniq hj₀ hval₀]
    rw [Set.ncard_image_of_injective _ ?_, Set.ncard_coe_finset, Finset.card_range]
    intro m₁ m₂ h
    have h1 : Nat.pair j₀ m₁ = Nat.pair j₀ m₂ := by
      have := congrArg Nat.unpair h
      simpa using this
    have := congrArg Nat.unpair h1
    simpa using this

theorem finite_padPoint_fiber (z : ℂ) : {i : ℕ | padPoint i = z}.Finite := by
  refine Set.Subsingleton.finite ?_
  intro i hi j hj
  exact padPoint_injective (by rw [hi, hj] : padPoint i = padPoint j)

theorem finite_slot_fiber {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ)
    (hmultsupp : ∀ z, mult z ≠ 0 → D z ≠ 0) {z : ℂ} (hz0 : z ≠ 0) :
    {n : ℕ | slot D hlf mult n
      ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z}.Finite := by
  classical
  by_cases hmz : mult z = 0
  · have hempty : {n : ℕ | slot D hlf mult n
        ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hslot, hvalue⟩
      have hm := hslot.2
      rw [hvalue, hmz] at hm
      omega
    rw [hempty]
    exact Set.finite_empty
  · obtain ⟨⟨k₀, j₀⟩, ⟨hj₀, hval₀⟩, huniq⟩ := exists_unique_shell hlf (hmultsupp z hmz) hz0
    rw [slot_fiber_eq hlf mult huniq hj₀ hval₀]
    exact (Finset.range (mult z)).finite_toSet.image _

theorem ncard_pad_fiber {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ) (z : ℂ) :
    {n : ℕ | ¬ slot D hlf mult n
        ∧ padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n) = z}.ncard
      = {i : ℕ | padPoint i = z}.ncard := by
  classical
  have hinf : {n : ℕ | ¬ slot D hlf mult n}.Infinite := infinite_compl_slot D hlf mult
  have himg : (Nat.count (fun m => ¬ slot D hlf mult m))
      '' {n : ℕ | ¬ slot D hlf mult n
          ∧ padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n) = z}
      = {i : ℕ | padPoint i = z} := by
    ext i
    constructor
    · rintro ⟨n, ⟨_, hval⟩, rfl⟩
      exact hval
    · intro hi
      refine ⟨Nat.nth (fun m => ¬ slot D hlf mult m) i,
        ⟨Nat.nth_mem_of_infinite hinf i, ?_⟩, Nat.count_nth_of_infinite hinf i⟩
      rw [Nat.count_nth_of_infinite hinf i]
      exact hi
  have hinj : Set.InjOn (Nat.count (fun m => ¬ slot D hlf mult m))
      {n : ℕ | ¬ slot D hlf mult n
        ∧ padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n) = z} := by
    intro n₁ h₁ n₂ h₂ h
    have e₁ : Nat.nth (fun m => ¬ slot D hlf mult m)
        (Nat.count (fun m => ¬ slot D hlf mult m) n₁) = n₁ := Nat.nth_count h₁.1
    have e₂ : Nat.nth (fun m => ¬ slot D hlf mult m)
        (Nat.count (fun m => ¬ slot D hlf mult m) n₂) = n₂ := Nat.nth_count h₂.1
    rw [← e₁, ← e₂, h]
  rw [← himg, Set.InjOn.ncard_image hinj]

theorem finite_pad_fiber {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ) (z : ℂ) :
    {n : ℕ | ¬ slot D hlf mult n
      ∧ padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n) = z}.Finite := by
  classical
  refine Set.Finite.subset ((finite_padPoint_fiber z).image
    (Nat.nth (fun m => ¬ slot D hlf mult m))) ?_
  rintro n ⟨hn, hval⟩
  exact ⟨Nat.count (fun m => ¬ slot D hlf mult m) n, hval, Nat.nth_count hn⟩

theorem zeroMultiplicity_divisorSeq {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ)
    (hmultsupp : ∀ z, mult z ≠ 0 → D z ≠ 0) {z : ℂ} (hz0 : z ≠ 0) :
    GaloisForLFunctions.zeroMultiplicity (divisorSeq D hlf mult) z
      = mult z + {i : ℕ | padPoint i = z}.ncard := by
  classical
  have hsplit : {n : ℕ | divisorSeq D hlf mult n = z}
      = {n : ℕ | slot D hlf mult n ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z}
        ∪ {n : ℕ | ¬ slot D hlf mult n
            ∧ padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n) = z} := by
    ext n
    by_cases h : slot D hlf mult n
    · simp [divisorSeq, h]
    · simp [divisorSeq, h]
  have hdisj : Disjoint
      {n : ℕ | slot D hlf mult n ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z}
      {n : ℕ | ¬ slot D hlf mult n
        ∧ padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n) = z} := by
    rw [Set.disjoint_left]
    rintro n ⟨hslot, _⟩ ⟨hnot, _⟩
    exact hnot hslot
  rw [GaloisForLFunctions.zeroMultiplicity, hsplit,
    Set.ncard_union_eq hdisj (finite_slot_fiber hlf mult hmultsupp hz0)
      (finite_pad_fiber hlf mult z),
    ncard_slot_fiber hlf mult hmultsupp hz0, ncard_pad_fiber hlf mult z]

theorem zeroMultiplicity_divisorSeq_zero {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D)
    (mult : ℂ → ℕ) : GaloisForLFunctions.zeroMultiplicity (divisorSeq D hlf mult) 0 = 0 := by
  have hempty : {n : ℕ | divisorSeq D hlf mult n = 0} = ∅ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact divisorSeq_ne_zero hlf mult n
  rw [GaloisForLFunctions.zeroMultiplicity, hempty, Set.ncard_empty]

theorem finite_norm_le_divisorSeq {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ)
    (hmultsupp : ∀ z, mult z ≠ 0 → D z ≠ 0) (R : ℝ) :
    {n : ℕ | ‖divisorSeq D hlf mult n‖ ≤ R}.Finite := by
  classical
  have hslotpart : {n : ℕ | slot D hlf mult n
      ∧ ‖shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1‖ ≤ R}.Finite := by
    have hcover : {n : ℕ | slot D hlf mult n
        ∧ ‖shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1‖ ≤ R}
        ⊆ ⋃ z ∈ {z : ℂ | D z ≠ 0 ∧ ‖z‖ ≤ R},
            {n : ℕ | slot D hlf mult n
              ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z} := by
      rintro n ⟨hslot, hnorm⟩
      refine Set.mem_biUnion (x := shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1)
        ⟨(shellPoint_mem hlf hslot.1).1, hnorm⟩ ⟨hslot, rfl⟩
    refine Set.Finite.subset (Set.Finite.biUnion (hlf R) fun z hz => ?_) hcover
    by_cases hz0 : z = 0
    · have hempty : {n : ℕ | slot D hlf mult n
          ∧ shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 = z} = ∅ := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨hslot, hvalue⟩
        have hmem := shellPoint_mem hlf hslot.1
        have hnorm := hmem.2.1
        rw [hvalue, hz0, norm_zero] at hnorm
        have hk : (0:ℝ) ≤ ((n.unpair.1 : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      rw [hempty]
      exact Set.finite_empty
    · exact finite_slot_fiber hlf mult hmultsupp hz0
  have hpadpart : {n : ℕ | ¬ slot D hlf mult n
      ∧ ‖padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n)‖ ≤ R}.Finite := by
    have hfin : {i : ℕ | ‖padPoint i‖ ≤ R}.Finite := by
      refine Set.Finite.subset (Set.finite_Icc 0 ⌈R⌉₊) ?_
      intro i hi
      simp only [Set.mem_setOf_eq, norm_padPoint] at hi
      simp only [Set.mem_Icc]
      refine ⟨Nat.zero_le _, ?_⟩
      have hiR : (i : ℝ) ≤ R := by linarith
      have hceil : ⌈(i : ℝ)⌉₊ ≤ ⌈R⌉₊ := Nat.ceil_le_ceil hiR
      rwa [Nat.ceil_natCast] at hceil
    refine Set.Finite.subset (hfin.image (Nat.nth (fun m => ¬ slot D hlf mult m))) ?_
    rintro n ⟨hn, hnorm⟩
    refine ⟨Nat.count (fun m => ¬ slot D hlf mult m) n, hnorm, ?_⟩
    exact Nat.nth_count (p := fun m => ¬ slot D hlf mult m) hn
  have hsplit : {n : ℕ | ‖divisorSeq D hlf mult n‖ ≤ R}
      ⊆ {n : ℕ | slot D hlf mult n
          ∧ ‖shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1‖ ≤ R}
        ∪ {n : ℕ | ¬ slot D hlf mult n
          ∧ ‖padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n)‖ ≤ R} := by
    intro n hn
    by_cases h : slot D hlf mult n
    · left
      refine ⟨h, ?_⟩
      have hval : divisorSeq D hlf mult n
          = shellPoint D hlf n.unpair.1 n.unpair.2.unpair.1 := by
        rw [divisorSeq, if_pos h]
      have hn' : ‖divisorSeq D hlf mult n‖ ≤ R := hn
      rwa [hval] at hn'
    · right
      refine ⟨h, ?_⟩
      have hval : divisorSeq D hlf mult n
          = padPoint (Nat.count (fun m => ¬ slot D hlf mult m) n) := by
        rw [divisorSeq, if_neg h]
      have hn' : ‖divisorSeq D hlf mult n‖ ≤ R := hn
      rwa [hval] at hn'
  exact Set.Finite.subset (hslotpart.union hpadpart) hsplit

theorem tendsto_norm_divisorSeq {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D) (mult : ℂ → ℕ)
    (hmultsupp : ∀ z, mult z ≠ 0 → D z ≠ 0) :
    Tendsto (fun n => ‖divisorSeq D hlf mult n‖) atTop atTop := by
  rw [tendsto_atTop]
  intro R
  have hfin := finite_norm_le_divisorSeq hlf mult hmultsupp R
  have hcof : ∀ᶠ n in Filter.cofinite, ¬ (‖divisorSeq D hlf mult n‖ ≤ R) :=
    Filter.eventually_cofinite.2 (by simpa using hfin)
  rw [Nat.cofinite_eq_atTop] at hcof
  filter_upwards [hcof] with n hn
  exact le_of_lt (not_le.1 hn)

/-- **Every locally finite signed divisor left of the line is presented by two sequences.** -/
theorem exists_presentation_of_locallyFiniteDivisor {D : ℂ → ℤ} (hlf : LocallyFiniteDivisor D)
    (hsupp : ∀ z : ℂ, D z ≠ 0 → z.re < 1) :
    ∃ a b : ℕ → ℂ, Tendsto (fun n => ‖a n‖) atTop atTop ∧ (∀ n, a n ≠ 0)
      ∧ (∀ n, (a n).re < 1) ∧ Tendsto (fun n => ‖b n‖) atTop atTop ∧ (∀ n, b n ≠ 0)
      ∧ (∀ n, (b n).re < 1)
      ∧ ∀ z : ℂ, ((GaloisForLFunctions.zeroMultiplicity a z : ℤ)
          - (GaloisForLFunctions.zeroMultiplicity b z : ℤ))
        = if z = 0 then 0 else D z := by
  classical
  set mz : ℂ → ℕ := fun z => (D z).toNat with hmzdef
  set mp : ℂ → ℕ := fun z => (-(D z)).toNat with hmpdef
  have hmzsupp : ∀ z, mz z ≠ 0 → D z ≠ 0 := by
    intro z hz h0
    rw [hmzdef] at hz
    simp only [h0] at hz
    exact hz rfl
  have hmpsupp : ∀ z, mp z ≠ 0 → D z ≠ 0 := by
    intro z hz h0
    rw [hmpdef] at hz
    simp only [h0] at hz
    exact hz (by simp)
  refine ⟨divisorSeq D hlf mz, divisorSeq D hlf mp,
    tendsto_norm_divisorSeq hlf mz hmzsupp, divisorSeq_ne_zero hlf mz,
    re_divisorSeq_lt_one hlf hsupp mz, tendsto_norm_divisorSeq hlf mp hmpsupp,
    divisorSeq_ne_zero hlf mp, re_divisorSeq_lt_one hlf hsupp mp, fun z => ?_⟩
  by_cases hz0 : z = 0
  · subst hz0
    rw [zeroMultiplicity_divisorSeq_zero hlf mz, zeroMultiplicity_divisorSeq_zero hlf mp,
      if_pos rfl]
    simp
  · rw [zeroMultiplicity_divisorSeq hlf mz hmzsupp hz0,
      zeroMultiplicity_divisorSeq hlf mp hmpsupp hz0, if_neg hz0]
    have hmzmp : ((mz z : ℤ) - (mp z : ℤ)) = D z := by
      show ((D z).toNat : ℤ) - ((-(D z)).toNat : ℤ) = D z
      omega
    push_cast
    linarith

/-- **Divisor surjectivity of the Helson continuation stratum, for an arbitrary locally finite
signed divisor supported strictly left of the line.** -/
theorem exists_continuable_phase_with_prescribed_locallyFinite_divisor {D : ℂ → ℤ}
    (hlf : LocallyFiniteDivisor D) (hsupp : ∀ z : ℂ, D z ≠ 0 → z.re < 1) :
    ∃ χ : PhaseTorus, χ ∈ continuableStratum ∧
      ∃ Z : ℂ → ℂ, MeromorphicOn Z Set.univ ∧
        (∀ s : ℂ, 1 < s.re →
          HasProd (fun p : Nat.Primes => (1 - (χ p : ℂ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹) (Z s)) ∧
        ∀ z : ℂ, meromorphicOrderAt Z z = ((D z : ℤ) : WithTop ℤ) := by
  classical
  obtain ⟨a, b, hatend, hane, hare, hbtend, hbne, hbre, hmult⟩ :=
    exists_presentation_of_locallyFiniteDivisor hlf hsupp
  obtain ⟨χ, hχ, Z, hZmero, hZprod, hZord⟩ :=
    exists_continuable_phase_with_divisor_at_origin (D 0) hatend hane hbtend hbne hare hbre
  refine ⟨χ, hχ, Z, hZmero, hZprod, fun z => ?_⟩
  rw [hZord z]
  have hdiff := hmult z
  by_cases hz0 : z = 0
  · subst hz0
    rw [if_pos rfl] at hdiff
    rw [if_pos rfl]
    have hz : ((GaloisForLFunctions.zeroMultiplicity a 0 : ℤ) : WithTop ℤ)
        - ((GaloisForLFunctions.zeroMultiplicity b 0 : ℤ) : WithTop ℤ) = 0 := by
      rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, hdiff]
      rfl
    rw [hz, add_zero]
  · rw [if_neg hz0] at hdiff
    rw [if_neg hz0]
    have hz : ((GaloisForLFunctions.zeroMultiplicity a z : ℤ) : WithTop ℤ)
        - ((GaloisForLFunctions.zeroMultiplicity b z : ℤ) : WithTop ℤ)
        = ((D z : ℤ) : WithTop ℤ) := by
      rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, hdiff]
    rw [hz, zero_add]

end RHTower

end
