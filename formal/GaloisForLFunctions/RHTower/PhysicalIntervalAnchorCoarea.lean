import GaloisForLFunctions.RHTower.CommonProfileBooleanAnchorCurvature

/-!
# The physical interval-anchor coarea and phase law

A finite family of weighted cells inside the physical aperture `(0, A)` produces, for every sieve
set `S`, the uncentered profile `F_S` and its mean-removed energy

```text
Energy(S) = ∫_0^A F_S² − L_S²/A,      L_S = ∫_0^A F_S.
```

Boolean inclusion–exclusion over an anchor set `C` disjoint from the base `N` turns the alternating
difference of these energies into the exact signed coarea law

```text
κ_C Energy(N) = U_{C,N} − B_{C,N}/A,
```

where both `U` and `B` are *manifestly nonnegative* double sums carrying the common-anchor factor.
Hence every negative physical anchor curvature comes from the single rank-one mean-removal channel.

The two-prime specialization then shows that the sign genuinely changes with the aperture: with the
actual weights `log m / m` at `m = 2, 3` there is exactly one transition aperture
`A_* = c(1 + 4 log 3/(3 log 2))`, strictly between `3c` and `4c`, where `c = log(4/3)`.
-/

namespace RHTower

open MeasureTheory Set
open scoped BigOperators

noncomputable section

/-! ## Cells inside the physical aperture -/

/-- The indicator of one physical cell. -/
def cellIndicator (lo hi : ℝ) : ℝ → ℝ := Set.indicator (Set.Ioc lo hi) (fun _ => 1)

theorem cellIndicator_mul (a b c d : ℝ) :
    (fun t => cellIndicator a b t * cellIndicator c d t)
      = cellIndicator (max a c) (min b d) := by
  funext t
  simp only [cellIndicator]
  rw [← Set.inter_indicator_mul, Set.Ioc_inter_Ioc]
  simp

theorem cellIndicator_nonneg (a b : ℝ) (t : ℝ) : 0 ≤ cellIndicator a b t := by
  simp only [cellIndicator, Set.indicator_apply]
  split <;> norm_num

theorem integrableOn_cellIndicator (a b A : ℝ) :
    IntegrableOn (cellIndicator a b) (Set.Ioc (0 : ℝ) A) volume := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
  · exact (measurable_const.indicator measurableSet_Ioc).aestronglyMeasurable
  · filter_upwards with t
    simp only [cellIndicator, Set.indicator_apply, Real.norm_eq_abs]
    split <;> norm_num

/-- The physical aperture pairing. -/
def anchorInner (A : ℝ) (f g : ℝ → ℝ) : ℝ := ∫ t in Set.Ioc (0 : ℝ) A, f t * g t

theorem anchorInner_cellIndicator (A a b c d : ℝ) :
    anchorInner A (cellIndicator a b) (cellIndicator c d)
      = volume.real (Set.Ioc (0 : ℝ) A ∩ Set.Ioc (max a c) (min b d)) := by
  rw [anchorInner, show (fun t => cellIndicator a b t * cellIndicator c d t)
      = cellIndicator (max a c) (min b d) from cellIndicator_mul a b c d]
  simp only [cellIndicator]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc, MeasureTheory.setIntegral_const]
  simp

theorem anchorInner_cellIndicator_nonneg (A a b c d : ℝ) :
    0 ≤ anchorInner A (cellIndicator a b) (cellIndicator c d) := by
  rw [anchorInner_cellIndicator]
  exact measureReal_nonneg

/-- The length of a cell inside the aperture. -/
def cellLength (A a b : ℝ) : ℝ := volume.real (Set.Ioc (0 : ℝ) A ∩ Set.Ioc a b)

theorem cellLength_nonneg (A a b : ℝ) : 0 ≤ cellLength A a b := measureReal_nonneg

theorem anchorInner_cellIndicator_one (A a b : ℝ) :
    anchorInner A (cellIndicator a b) (fun _ => 1) = cellLength A a b := by
  rw [anchorInner, cellLength]
  simp only [mul_one, cellIndicator]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc, MeasureTheory.setIntegral_const]
  simp

end

namespace PhysicalAnchor

noncomputable section

open scoped InnerProductSpace

variable {ι κ : Type*}

/-! ## Gram energies of a sifted cell packet -/

/-- The sifted energy of a finite packet relative to an arbitrary real Gram kernel. -/
def gramSiftedEnergy (indices : Finset κ) (s : Finset ι)
    (coordinate : ι → κ → ℝ) (G : κ → κ → ℝ) : ℝ :=
  ∑ x ∈ indices, ∑ y ∈ indices,
    coordinatePacketWeight s coordinate x * coordinatePacketWeight s coordinate y * G x y

/-- Reweighting of a Gram kernel by a source amplitude. -/
def weightedGram (w : κ → ℝ) (G : κ → κ → ℝ) (x y : κ) : ℝ := w x * w y * G x y

/-- **Boolean anchor-curvature law for an arbitrary Gram kernel.**  The alternating finite
difference of sifted energies over the powerset of an anchor set disjoint from the base equals
the double sum carrying the common-anchor factor.  The proof is finite inclusion–exclusion. -/
theorem gramBooleanAnchorCurvature [DecidableEq ι]
    (indices : Finset κ) (base anchor : Finset ι) (hdisj : Disjoint base anchor)
    (coordinate : ι → κ → ℝ) (G : κ → κ → ℝ) :
    (∑ d ∈ anchor.powerset,
      (-1 : ℝ) ^ d.card * gramSiftedEnergy indices (base ∪ d) coordinate G) =
      ∑ x ∈ indices, ∑ y ∈ indices,
        coordinatePacketWeight base coordinate x * coordinatePacketWeight base coordinate y *
          commonAnchorWeight anchor coordinate x y * G x y := by
  classical
  have key : ∀ x y : κ,
      (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
        (coordinatePacketWeight (base ∪ d) coordinate x *
          coordinatePacketWeight (base ∪ d) coordinate y * G x y)) =
        coordinatePacketWeight base coordinate x * coordinatePacketWeight base coordinate y *
          commonAnchorWeight anchor coordinate x y * G x y := by
    intro x y
    rw [← sum_powerset_signed_commonCoordinateWeight anchor coordinate x y,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdsub : d ⊆ anchor := Finset.mem_powerset.mp hd
    have hbd : Disjoint base d := by
      rw [Finset.disjoint_left]
      intro p hpbase hpd
      exact (Finset.disjoint_left.mp hdisj hpbase (hdsub hpd))
    rw [coordinatePacketWeight_union hbd, coordinatePacketWeight_union hbd]
    ring
  simp_rw [gramSiftedEnergy, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact key x y

/-! ## The physical cell packet -/

/-- The uncentered sifted profile of a cell packet. -/
def siftedProfile (indices : Finset κ) (s : Finset ι) (coordinate : ι → κ → ℝ)
    (w lo hi : κ → ℝ) : ℝ → ℝ :=
  fun t => ∑ m ∈ indices,
    coordinatePacketWeight s coordinate m * w m * cellIndicator (lo m) (hi m) t

/-- The total mass of the uncentered sifted profile inside the aperture. -/
def siftedMass (A : ℝ) (indices : Finset κ) (s : Finset ι) (coordinate : ι → κ → ℝ)
    (w lo hi : κ → ℝ) : ℝ :=
  ∑ m ∈ indices, coordinatePacketWeight s coordinate m * w m * cellLength A (lo m) (hi m)

/-- The overlap Gram kernel of the cells inside the aperture. -/
def apertureGram (A : ℝ) (lo hi : κ → ℝ) (x y : κ) : ℝ :=
  anchorInner A (cellIndicator (lo x) (hi x)) (cellIndicator (lo y) (hi y))

/-- The rank-one centering Gram kernel. -/
def centeringGram (A : ℝ) (lo hi : κ → ℝ) (x y : κ) : ℝ :=
  cellLength A (lo x) (hi x) * cellLength A (lo y) (hi y)

/-- The centered Gram kernel of the physical cell packet. -/
def centeredGram (A : ℝ) (lo hi : κ → ℝ) (x y : κ) : ℝ :=
  apertureGram A lo hi x y - centeringGram A lo hi x y / A

/-- The physical packet energy: the squared aperture norm of the mean-removed sifted profile. -/
def physicalEnergy (A : ℝ) (indices : Finset κ) (s : Finset ι) (coordinate : ι → κ → ℝ)
    (w lo hi : κ → ℝ) : ℝ :=
  gramSiftedEnergy indices s coordinate (weightedGram w (centeredGram A lo hi))

theorem integrableOn_cellIndicator_mul (A a b c d : ℝ) :
    IntegrableOn (fun t => cellIndicator a b t * cellIndicator c d t)
      (Set.Ioc (0 : ℝ) A) volume := by
  rw [cellIndicator_mul]
  exact integrableOn_cellIndicator _ _ _

/-- The aperture integral of the squared sifted profile is the uncentered Gram energy. -/
theorem integral_siftedProfile_sq (A : ℝ) (indices : Finset κ) (s : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) :
    (∫ t in Set.Ioc (0 : ℝ) A,
        siftedProfile indices s coordinate w lo hi t *
          siftedProfile indices s coordinate w lo hi t) =
      gramSiftedEnergy indices s coordinate (weightedGram w (apertureGram A lo hi)) := by
  classical
  set c : κ → ℝ := fun m => coordinatePacketWeight s coordinate m * w m with hc
  have hpt : ∀ t : ℝ,
      siftedProfile indices s coordinate w lo hi t *
          siftedProfile indices s coordinate w lo hi t =
        ∑ m ∈ indices, ∑ n ∈ indices,
          c m * c n * (cellIndicator (lo m) (hi m) t * cellIndicator (lo n) (hi n) t) := by
    intro t
    simp only [siftedProfile, hc]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring
  simp only [hpt]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [MeasureTheory.integral_const_mul]
      simp only [weightedGram, apertureGram, anchorInner, hc]
      ring
    · intro n _
      exact ((integrableOn_cellIndicator_mul A (lo m) (hi m) (lo n) (hi n)).const_mul _)
  · intro m _
    refine MeasureTheory.integrable_finsetSum _ fun n _ => ?_
    exact ((integrableOn_cellIndicator_mul A (lo m) (hi m) (lo n) (hi n)).const_mul _)

/-- The aperture integral of the sifted profile is its total mass. -/
theorem integral_siftedProfile (A : ℝ) (indices : Finset κ) (s : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) :
    (∫ t in Set.Ioc (0 : ℝ) A, siftedProfile indices s coordinate w lo hi t) =
      siftedMass A indices s coordinate w lo hi := by
  classical
  simp only [siftedProfile, siftedMass]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [MeasureTheory.integral_const_mul]
    congr 1
    have := anchorInner_cellIndicator_one A (lo m) (hi m)
    simpa [anchorInner] using this
  · intro m _
    exact (integrableOn_cellIndicator (lo m) (hi m) A).const_mul _

/-- The Gram expansion of the rank-one centering kernel is the squared total mass. -/
theorem gramSiftedEnergy_centering (A : ℝ) (indices : Finset κ) (s : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) :
    gramSiftedEnergy indices s coordinate (weightedGram w (centeringGram A lo hi)) =
      (siftedMass A indices s coordinate w lo hi) ^ 2 := by
  classical
  simp only [gramSiftedEnergy, weightedGram, centeringGram, siftedMass, sq]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => by ring

/-- **(PI1)  Orthogonal mean removal.**  The physical packet energy is the uncentered aperture
energy minus the rank-one centering mass. -/
theorem physicalEnergy_eq_integral_sub (A : ℝ) (indices : Finset κ) (s : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) :
    physicalEnergy A indices s coordinate w lo hi =
      (∫ t in Set.Ioc (0 : ℝ) A,
        siftedProfile indices s coordinate w lo hi t *
          siftedProfile indices s coordinate w lo hi t) -
        (siftedMass A indices s coordinate w lo hi) ^ 2 / A := by
  classical
  rw [integral_siftedProfile_sq, ← gramSiftedEnergy_centering A indices s coordinate w lo hi]
  have hsub : ∀ G H : κ → κ → ℝ,
      gramSiftedEnergy indices s coordinate (fun x y => G x y - H x y)
        = gramSiftedEnergy indices s coordinate G - gramSiftedEnergy indices s coordinate H := by
    intro G H
    simp only [gramSiftedEnergy, mul_sub, Finset.sum_sub_distrib]
  have hdiv : ∀ H : κ → κ → ℝ,
      gramSiftedEnergy indices s coordinate (fun x y => H x y / A)
        = gramSiftedEnergy indices s coordinate H / A := by
    intro H
    simp only [gramSiftedEnergy, Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have e1 : weightedGram w (centeredGram A lo hi)
      = fun x y => weightedGram w (apertureGram A lo hi) x y
          - weightedGram w (centeringGram A lo hi) x y / A := by
    funext x y
    simp only [weightedGram, centeredGram]
    ring
  rw [physicalEnergy, e1, hsub, hdiv]

/-! ## The Boolean-cover coarea law -/

/-- The Boolean-cover overlap mass of an anchor set: the anchored uncentered Gram mass. -/
def anchorCoareaMass (A : ℝ) (indices : Finset κ) (base anchor : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) : ℝ :=
  ∑ x ∈ indices, ∑ y ∈ indices,
    coordinatePacketWeight base coordinate x * coordinatePacketWeight base coordinate y *
      commonAnchorWeight anchor coordinate x y * weightedGram w (apertureGram A lo hi) x y

/-- The Boolean-cover centering mass of an anchor set: the anchored rank-one Gram mass. -/
def anchorCenteringMass (A : ℝ) (indices : Finset κ) (base anchor : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) : ℝ :=
  ∑ x ∈ indices, ∑ y ∈ indices,
    coordinatePacketWeight base coordinate x * coordinatePacketWeight base coordinate y *
      commonAnchorWeight anchor coordinate x y * weightedGram w (centeringGram A lo hi) x y

/-- **(PI3), first half.**  The alternating sum of uncentered aperture energies is the anchored
overlap mass. -/
theorem alternating_integral_sq_eq_anchorCoareaMass [DecidableEq ι]
    (A : ℝ) (indices : Finset κ) (base anchor : Finset ι) (hdisj : Disjoint base anchor)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) :
    (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
      ∫ t in Set.Ioc (0 : ℝ) A,
        siftedProfile indices (base ∪ d) coordinate w lo hi t *
          siftedProfile indices (base ∪ d) coordinate w lo hi t) =
      anchorCoareaMass A indices base anchor coordinate w lo hi := by
  classical
  simp only [integral_siftedProfile_sq]
  exact gramBooleanAnchorCurvature indices base anchor hdisj coordinate
    (weightedGram w (apertureGram A lo hi))

/-- **(PI3), second half.**  The alternating sum of squared masses is the anchored centering
mass. -/
theorem alternating_mass_sq_eq_anchorCenteringMass [DecidableEq ι]
    (A : ℝ) (indices : Finset κ) (base anchor : Finset ι) (hdisj : Disjoint base anchor)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) :
    (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
      (siftedMass A indices (base ∪ d) coordinate w lo hi) ^ 2) =
      anchorCenteringMass A indices base anchor coordinate w lo hi := by
  classical
  simp only [← gramSiftedEnergy_centering]
  exact gramBooleanAnchorCurvature indices base anchor hdisj coordinate
    (weightedGram w (centeringGram A lo hi))

theorem coordinatePacketWeight_nonneg {s : Finset ι} {coordinate : ι → κ → ℝ}
    (hcoord : ∀ p x, 0 ≤ coordinate p x) (x : κ) :
    0 ≤ coordinatePacketWeight s coordinate x :=
  Finset.prod_nonneg fun p _ => hcoord p x

theorem commonAnchorWeight_nonneg {anchor : Finset ι} {coordinate : ι → κ → ℝ}
    (hcoord : ∀ p x, coordinate p x = 0 ∨ coordinate p x = 1) (x y : κ) :
    0 ≤ commonAnchorWeight anchor coordinate x y := by
  refine Finset.prod_nonneg fun p _ => ?_
  rcases hcoord p x with h | h <;> rcases hcoord p y with h' | h' <;> simp [h, h']

/-- **(PI3), nonnegativity of the overlap mass.** -/
theorem anchorCoareaMass_nonneg (A : ℝ) (indices : Finset κ) (base anchor : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ)
    (hcoord : ∀ p x, coordinate p x = 0 ∨ coordinate p x = 1) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ anchorCoareaMass A indices base anchor coordinate w lo hi := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  have hcnn : ∀ p x, 0 ≤ coordinate p x := by
    intro p x; rcases hcoord p x with h | h <;> simp [h]
  have h1 : 0 ≤ coordinatePacketWeight base coordinate x *
      coordinatePacketWeight base coordinate y * commonAnchorWeight anchor coordinate x y :=
    mul_nonneg (mul_nonneg (coordinatePacketWeight_nonneg hcnn x)
      (coordinatePacketWeight_nonneg hcnn y)) (commonAnchorWeight_nonneg hcoord x y)
  refine mul_nonneg h1 ?_
  exact mul_nonneg (mul_nonneg (hw x) (hw y)) (anchorInner_cellIndicator_nonneg _ _ _ _ _)

/-- **(PI3), nonnegativity of the centering mass.** -/
theorem anchorCenteringMass_nonneg (A : ℝ) (indices : Finset κ) (base anchor : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ)
    (hcoord : ∀ p x, coordinate p x = 0 ∨ coordinate p x = 1) (hw : ∀ x, 0 ≤ w x) :
    0 ≤ anchorCenteringMass A indices base anchor coordinate w lo hi := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  have hcnn : ∀ p x, 0 ≤ coordinate p x := by
    intro p x; rcases hcoord p x with h | h <;> simp [h]
  have h1 : 0 ≤ coordinatePacketWeight base coordinate x *
      coordinatePacketWeight base coordinate y * commonAnchorWeight anchor coordinate x y :=
    mul_nonneg (mul_nonneg (coordinatePacketWeight_nonneg hcnn x)
      (coordinatePacketWeight_nonneg hcnn y)) (commonAnchorWeight_nonneg hcoord x y)
  refine mul_nonneg h1 ?_
  exact mul_nonneg (mul_nonneg (hw x) (hw y))
    (mul_nonneg (cellLength_nonneg _ _ _) (cellLength_nonneg _ _ _))

/-- **(PI4)  Exact signed coarea law.**  The Boolean anchor curvature of the physical packet
energy is the nonnegative anchored overlap mass minus the nonnegative anchored centering mass
divided by the aperture. -/
theorem physicalAnchorCurvature_eq [DecidableEq ι]
    (A : ℝ) (indices : Finset κ) (base anchor : Finset ι) (hdisj : Disjoint base anchor)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) :
    (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
      physicalEnergy A indices (base ∪ d) coordinate w lo hi) =
      anchorCoareaMass A indices base anchor coordinate w lo hi -
        anchorCenteringMass A indices base anchor coordinate w lo hi / A := by
  classical
  rw [show (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
      physicalEnergy A indices (base ∪ d) coordinate w lo hi) =
      ∑ x ∈ indices, ∑ y ∈ indices,
        coordinatePacketWeight base coordinate x * coordinatePacketWeight base coordinate y *
          commonAnchorWeight anchor coordinate x y *
            weightedGram w (centeredGram A lo hi) x y from
    gramBooleanAnchorCurvature indices base anchor hdisj coordinate
      (weightedGram w (centeredGram A lo hi))]
  simp only [anchorCoareaMass, anchorCenteringMass, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [weightedGram, centeredGram]
  ring

/-- The dimensionless anchored overlap concentration. -/
def anchorOverlapConcentration (A : ℝ) (indices : Finset κ) (base anchor : Finset ι)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) : ℝ :=
  A * anchorCoareaMass A indices base anchor coordinate w lo hi /
    anchorCenteringMass A indices base anchor coordinate w lo hi

/-- **(PI6)  Complete sign classification.**  When the anchored centering mass is positive the
Boolean anchor curvature is a positive multiple of the overlap-concentration defect. -/
theorem physicalAnchorCurvature_eq_concentration_defect [DecidableEq ι]
    (A : ℝ) (indices : Finset κ) (base anchor : Finset ι) (hdisj : Disjoint base anchor)
    (coordinate : ι → κ → ℝ) (w lo hi : κ → ℝ) (hA : A ≠ 0)
    (hB : anchorCenteringMass A indices base anchor coordinate w lo hi ≠ 0) :
    (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
      physicalEnergy A indices (base ∪ d) coordinate w lo hi) =
      anchorCenteringMass A indices base anchor coordinate w lo hi / A *
        (anchorOverlapConcentration A indices base anchor coordinate w lo hi - 1) := by
  rw [physicalAnchorCurvature_eq A indices base anchor hdisj coordinate w lo hi,
    anchorOverlapConcentration]
  field_simp

/-! ## Explicit cell lengths and overlaps -/

theorem measureReal_Ioc_of_le {x y : ℝ} (h : x ≤ y) : volume.real (Set.Ioc x y) = y - x := by
  rw [MeasureTheory.measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]

theorem measureReal_Ioc_of_ge {x y : ℝ} (h : y ≤ x) : volume.real (Set.Ioc x y) = 0 := by
  rw [Set.Ioc_eq_empty (by simpa using h)]
  simp

theorem cellLength_of_subset {A a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hbA : b ≤ A) :
    cellLength A a b = b - a := by
  rw [cellLength, Set.Ioc_inter_Ioc, max_eq_right h0, min_eq_right hbA, measureReal_Ioc_of_le hab]

theorem anchorInner_cell_self {A a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (hbA : b ≤ A) :
    anchorInner A (cellIndicator a b) (cellIndicator a b) = b - a := by
  rw [anchorInner_cellIndicator, max_self, min_self]
  exact cellLength_of_subset h0 hab hbA

theorem anchorInner_cell_disjoint {A a b c d : ℝ} (h : b ≤ c) :
    anchorInner A (cellIndicator a b) (cellIndicator c d) = 0 := by
  rw [anchorInner_cellIndicator, Set.Ioc_inter_Ioc]
  refine measureReal_Ioc_of_ge ?_
  calc min A (min b d) ≤ min b d := min_le_right _ _
    _ ≤ b := min_le_left _ _
    _ ≤ c := h
    _ ≤ max a c := le_max_right _ _
    _ ≤ max 0 (max a c) := le_max_right _ _

/-! ## The complete physical two-prime packet -/

/-- The common cell width `log(4/3)` of the complete physical packet with `M = 3`, `K = 4`. -/
def physCellWidth : ℝ := Real.log (4 / 3)

/-- The gap `log(3/2)` between the two physical cells. -/
def physGap : ℝ := Real.log (3 / 2)

/-- Left endpoint `log(3/m)` of the physical cell of the atom `m`. -/
def physLo : ℕ → ℝ := fun m => Real.log (3 / (m : ℝ))

/-- Right endpoint `log(4/m)` of the physical cell of the atom `m`. -/
def physHi : ℕ → ℝ := fun m => Real.log (4 / (m : ℝ))

/-- The physical logarithmic weight `log(m)/m`. -/
def physWeight : ℕ → ℝ := fun m => Real.log m / m

/-- The two atoms with nonempty physical cell and nonzero weight. -/
def physAtoms : Finset ℕ := {2, 3}

/-- The Boolean sieve coordinate `1_{p ∤ m}`. -/
def avoidCoordinate : ℕ → ℕ → ℝ := fun p m => if p ∣ m then 0 else 1

theorem avoidCoordinate_zero_or_one (p m : ℕ) :
    avoidCoordinate p m = 0 ∨ avoidCoordinate p m = 1 := by
  unfold avoidCoordinate; split <;> simp

theorem physWeight_nonneg (m : ℕ) : 0 ≤ physWeight m := by
  unfold physWeight
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · exact div_nonneg (Real.log_natCast_nonneg m) (Nat.cast_nonneg m)

theorem physCellWidth_pos : 0 < physCellWidth := Real.log_pos (by norm_num)

theorem physGap_pos : 0 < physGap := Real.log_pos (by norm_num)

theorem physCellWidth_lt_physGap : physCellWidth < physGap :=
  Real.log_lt_log (by norm_num) (by norm_num)

theorem physGap_add_physCellWidth : physGap + physCellWidth = Real.log 2 := by
  rw [physGap, physCellWidth, ← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

theorem physCellWidth_lt_log_two : physCellWidth < Real.log 2 := by
  have := physGap_pos
  have := physGap_add_physCellWidth
  linarith

@[simp] theorem physLo_three : physLo 3 = 0 := by
  simp [physLo]

@[simp] theorem physHi_three : physHi 3 = physCellWidth := by
  norm_num [physLo, physHi, physCellWidth]

@[simp] theorem physLo_two : physLo 2 = physGap := by
  norm_num [physLo, physGap]

@[simp] theorem physHi_two : physHi 2 = Real.log 2 := by
  norm_num [physHi]

theorem physWeight_two : physWeight 2 = Real.log 2 / 2 := by
  norm_num [physWeight]

theorem physWeight_three : physWeight 3 = Real.log 3 / 3 := by
  norm_num [physWeight]

theorem physWeight_two_pos : 0 < physWeight 2 := by
  rw [physWeight_two]
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

theorem physWeight_three_pos : 0 < physWeight 3 := by
  rw [physWeight_three]
  exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- `log 2 / 2 < log 3 / 3`, equivalently `8 < 9`. -/
theorem physWeight_two_lt_three : physWeight 2 < physWeight 3 := by
  have h8 : Real.log 8 < Real.log 9 := Real.log_lt_log (by norm_num) (by norm_num)
  have e8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have e9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [physWeight_two, physWeight_three]
  rw [e8, e9] at h8
  linarith

/-- `2 log 3 / 3 < 3 log 2 / 2`, equivalently `3^4 < 2^9`. -/
theorem two_physWeight_three_lt_three_physWeight_two :
    2 * physWeight 3 < 3 * physWeight 2 := by
  have h : Real.log 81 < Real.log 512 := Real.log_lt_log (by norm_num) (by norm_num)
  have e81 : Real.log 81 = 4 * Real.log 3 := by
    rw [show (81 : ℝ) = 3 ^ (4 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have e512 : Real.log 512 = 9 * Real.log 2 := by
    rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [physWeight_two, physWeight_three]
  rw [e81, e512] at h
  linarith

/-- `log 2 < 3 log(4/3)`, equivalently `2 < 64/27`. -/
theorem log_two_lt_three_physCellWidth : Real.log 2 < 3 * physCellWidth := by
  have h : Real.log 2 < Real.log (64 / 27) := Real.log_lt_log (by norm_num) (by norm_num)
  have e : Real.log (64 / 27) = 3 * physCellWidth := by
    rw [physCellWidth, show (64 : ℝ) / 27 = (4 / 3) ^ (3 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  rw [← e]
  exact h

theorem anchorInner_cell_disjoint' {A a b c d : ℝ} (h : d ≤ a) :
    anchorInner A (cellIndicator a b) (cellIndicator c d) = 0 := by
  rw [anchorInner_cellIndicator, Set.Ioc_inter_Ioc]
  refine measureReal_Ioc_of_ge ?_
  calc min A (min b d) ≤ min b d := min_le_right _ _
    _ ≤ d := min_le_right _ _
    _ ≤ a := h
    _ ≤ max a c := le_max_left _ _
    _ ≤ max 0 (max a c) := le_max_right _ _

/-! ## The physical Gram matrix -/

theorem physGap_le_log_two : physGap ≤ Real.log 2 := by
  have := physGap_add_physCellWidth
  have := physCellWidth_pos
  linarith

theorem cellLength_phys_three {A : ℝ} (hA : Real.log 2 ≤ A) :
    cellLength A (physLo 3) (physHi 3) = physCellWidth := by
  rw [physLo_three, physHi_three,
    cellLength_of_subset le_rfl physCellWidth_pos.le
      (le_trans physCellWidth_lt_log_two.le hA)]
  ring

theorem cellLength_phys_two {A : ℝ} (hA : Real.log 2 ≤ A) :
    cellLength A (physLo 2) (physHi 2) = physCellWidth := by
  rw [physLo_two, physHi_two,
    cellLength_of_subset physGap_pos.le physGap_le_log_two hA]
  linarith [physGap_add_physCellWidth]

theorem apertureGram_phys_three_three {A : ℝ} (hA : Real.log 2 ≤ A) :
    apertureGram A physLo physHi 3 3 = physCellWidth := by
  simp only [apertureGram, physLo_three, physHi_three]
  rw [anchorInner_cell_self le_rfl physCellWidth_pos.le
    (le_trans physCellWidth_lt_log_two.le hA)]
  ring

theorem apertureGram_phys_two_two {A : ℝ} (hA : Real.log 2 ≤ A) :
    apertureGram A physLo physHi 2 2 = physCellWidth := by
  simp only [apertureGram, physLo_two, physHi_two]
  rw [anchorInner_cell_self physGap_pos.le physGap_le_log_two hA]
  linarith [physGap_add_physCellWidth]

theorem apertureGram_phys_three_two {A : ℝ} : apertureGram A physLo physHi 3 2 = 0 := by
  simp only [apertureGram, physLo_three, physHi_three, physLo_two, physHi_two]
  exact anchorInner_cell_disjoint physCellWidth_lt_physGap.le

theorem apertureGram_phys_two_three {A : ℝ} : apertureGram A physLo physHi 2 3 = 0 := by
  simp only [apertureGram, physLo_three, physHi_three, physLo_two, physHi_two]
  exact anchorInner_cell_disjoint' physCellWidth_lt_physGap.le

/-- **(PI11)** The centered physical Gram matrix of the two-atom packet. -/
theorem centeredGram_phys {A : ℝ} (hA : Real.log 2 ≤ A) :
    centeredGram A physLo physHi 3 3 = physCellWidth - physCellWidth ^ 2 / A ∧
      centeredGram A physLo physHi 2 2 = physCellWidth - physCellWidth ^ 2 / A ∧
        centeredGram A physLo physHi 2 3 = -(physCellWidth ^ 2 / A) ∧
          centeredGram A physLo physHi 3 2 = -(physCellWidth ^ 2 / A) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [centeredGram, centeringGram, apertureGram_phys_three_three hA,
      apertureGram_phys_two_two hA, apertureGram_phys_two_three, apertureGram_phys_three_two,
      cellLength_phys_two hA, cellLength_phys_three hA] <;>
    ring

/-! ## The complete two-prime aperture phase law -/

theorem coordinatePacketWeight_empty_phys (m : ℕ) :
    coordinatePacketWeight (∅ : Finset ℕ) avoidCoordinate m = 1 := by
  simp [coordinatePacketWeight]

theorem coordinatePacketWeight_two_phys_two :
    coordinatePacketWeight ({2} : Finset ℕ) avoidCoordinate 2 = 0 := by
  simp [coordinatePacketWeight, avoidCoordinate]

theorem coordinatePacketWeight_two_phys_three :
    coordinatePacketWeight ({2} : Finset ℕ) avoidCoordinate 3 = 1 := by
  norm_num [coordinatePacketWeight, avoidCoordinate]

/-- The physical packet energy of an arbitrary sieve set in terms of the two surviving atoms. -/
theorem physicalEnergy_phys {A : ℝ} (hA : Real.log 2 ≤ A) (S : Finset ℕ) :
    physicalEnergy A physAtoms S avoidCoordinate physWeight physLo physHi =
      (coordinatePacketWeight S avoidCoordinate 2 * physWeight 2) ^ 2 *
          (physCellWidth - physCellWidth ^ 2 / A) -
        2 * (coordinatePacketWeight S avoidCoordinate 2 * physWeight 2) *
          (coordinatePacketWeight S avoidCoordinate 3 * physWeight 3) *
            (physCellWidth ^ 2 / A) +
        (coordinatePacketWeight S avoidCoordinate 3 * physWeight 3) ^ 2 *
          (physCellWidth - physCellWidth ^ 2 / A) := by
  obtain ⟨g33, g22, g23, g32⟩ := centeredGram_phys (A := A) hA
  simp only [physicalEnergy, gramSiftedEnergy, physAtoms, weightedGram]
  rw [Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3)]
  rw [Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3),
    Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3)]
  rw [g33, g22, g23, g32]
  ring

/-- The transition aperture `A_* = c(1 + 2a/b)`. -/
def physTransitionAperture : ℝ :=
  physCellWidth * (1 + 2 * physWeight 3 / physWeight 2)

/-- **(PI12)** The complete physical one-anchor curvature of the two-prime packet. -/
theorem physicalTwoPrimeCurvature {A : ℝ} (hA : Real.log 2 ≤ A) :
    (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
      physicalEnergy A physAtoms (∅ ∪ d) avoidCoordinate physWeight physLo physHi) =
      physWeight 2 * physCellWidth / A *
        (physWeight 2 * (A - physCellWidth) - 2 * physWeight 3 * physCellWidth) := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le (Real.log_pos (by norm_num)) hA
  rw [show ({2} : Finset ℕ).powerset = {∅, {2}} from by decide, Finset.sum_pair (by simp)]
  rw [Finset.card_empty, Finset.card_singleton]
  rw [Finset.empty_union, Finset.empty_union]
  rw [physicalEnergy_phys hA, physicalEnergy_phys hA]
  rw [coordinatePacketWeight_empty_phys, coordinatePacketWeight_empty_phys,
    coordinatePacketWeight_two_phys_two, coordinatePacketWeight_two_phys_three]
  field_simp
  ring

/-- **(PI13)** The curvature is a positive multiple of the aperture defect `A − A_*`. -/
theorem physicalTwoPrimeCurvature_eq_defect {A : ℝ} (hA : Real.log 2 ≤ A) :
    (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
      physicalEnergy A physAtoms (∅ ∪ d) avoidCoordinate physWeight physLo physHi) =
      physWeight 2 ^ 2 * physCellWidth / A * (A - physTransitionAperture) := by
  rw [physicalTwoPrimeCurvature hA, physTransitionAperture]
  have hb := physWeight_two_pos.ne'
  field_simp
  ring

theorem physicalTwoPrimeCurvature_coefficient_pos {A : ℝ} (hA : Real.log 2 ≤ A) :
    0 < physWeight 2 ^ 2 * physCellWidth / A := by
  have hA0 : (0 : ℝ) < A := lt_of_lt_of_le (Real.log_pos (by norm_num)) hA
  exact div_pos (mul_pos (pow_pos physWeight_two_pos 2) physCellWidth_pos) hA0

theorem mul_sign_iff {C x : ℝ} (hC : 0 < C) :
    (C * x < 0 ↔ x < 0) ∧ (C * x = 0 ↔ x = 0) ∧ (0 < C * x ↔ 0 < x) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_neg_iff]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · exact absurd h (not_lt.mpr hC.le)
    · exact fun h => Or.inl ⟨hC, h⟩
  · rw [mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hC.ne'
      · exact h
    · exact fun h => Or.inr h
  · rw [mul_pos_iff]
    constructor
    · rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact h
      · exact absurd h (not_lt.mpr hC.le)
    · exact fun h => Or.inl ⟨hC, h⟩

/-- **(PI14)** The complete aperture phase law: exactly one transition aperture, with strictly
negative curvature below it and strictly positive curvature above it. -/
theorem physicalTwoPrimeCurvature_phase_law {A : ℝ} (hA : Real.log 2 ≤ A) :
    ((∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy A physAtoms (∅ ∪ d) avoidCoordinate physWeight physLo physHi) < 0 ↔
      A < physTransitionAperture) ∧
    ((∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy A physAtoms (∅ ∪ d) avoidCoordinate physWeight physLo physHi) = 0 ↔
      A = physTransitionAperture) ∧
    (0 < (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy A physAtoms (∅ ∪ d) avoidCoordinate physWeight physLo physHi) ↔
      physTransitionAperture < A) := by
  have hC := physicalTwoPrimeCurvature_coefficient_pos hA
  rw [physicalTwoPrimeCurvature_eq_defect hA]
  obtain ⟨h1, h2, h3⟩ := mul_sign_iff (x := A - physTransitionAperture) hC
  refine ⟨?_, ?_, ?_⟩
  · rw [h1]; constructor <;> intro h <;> linarith
  · rw [h2]; constructor <;> intro h <;> linarith
  · rw [h3]; constructor <;> intro h <;> linarith

/-- **(PI15)** The transition aperture is strictly between `3c` and `4c`. -/
theorem physTransitionAperture_mem_Ioo :
    3 * physCellWidth < physTransitionAperture ∧
      physTransitionAperture < 4 * physCellWidth := by
  have hb := physWeight_two_pos
  have hc := physCellWidth_pos
  constructor
  · have key : 2 < 2 * physWeight 3 / physWeight 2 := by
      rw [lt_div_iff₀ hb]
      linarith [physWeight_two_lt_three]
    rw [physTransitionAperture]
    nlinarith
  · have key : 2 * physWeight 3 / physWeight 2 < 3 := by
      rw [div_lt_iff₀ hb]
      linarith [two_physWeight_three_lt_three_physWeight_two]
    rw [physTransitionAperture]
    nlinarith

/-- **(PI16)** Both integer apertures `3c` and `4c` lie in the full-cell range and realize the
two curvature signs. -/
theorem physicalTwoPrimeCurvature_sign_witnesses :
    Real.log 2 ≤ 3 * physCellWidth ∧ Real.log 2 ≤ 4 * physCellWidth ∧
      (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy (3 * physCellWidth) physAtoms (∅ ∪ d) avoidCoordinate physWeight
          physLo physHi) < 0 ∧
      0 < (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy (4 * physCellWidth) physAtoms (∅ ∪ d) avoidCoordinate physWeight
          physLo physHi) := by
  have h3 : Real.log 2 ≤ 3 * physCellWidth := log_two_lt_three_physCellWidth.le
  have h4 : Real.log 2 ≤ 4 * physCellWidth := by
    linarith [physCellWidth_pos, log_two_lt_three_physCellWidth]
  obtain ⟨hlo, hhi⟩ := physTransitionAperture_mem_Ioo
  exact ⟨h3, h4, (physicalTwoPrimeCurvature_phase_law h3).1.mpr hlo,
    (physicalTwoPrimeCurvature_phase_law h4).2.2.mpr hhi⟩

/-- **Falsification of the physical anchor-sign conjecture.**  The complete physical packet with
`M = 3`, `K = 4` has a one-anchor Boolean curvature that is strictly negative at one admissible
aperture and strictly positive at another. -/
theorem physical_anchor_sign_conjecture_false :
    ∃ A₀ A₁ : ℝ, Real.log 2 ≤ A₀ ∧ Real.log 2 ≤ A₁ ∧
      (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy A₀ physAtoms (∅ ∪ d) avoidCoordinate physWeight physLo physHi) < 0 ∧
      0 < (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy A₁ physAtoms (∅ ∪ d) avoidCoordinate physWeight physLo physHi) := by
  obtain ⟨h3, h4, hneg, hpos⟩ := physicalTwoPrimeCurvature_sign_witnesses
  exact ⟨3 * physCellWidth, 4 * physCellWidth, h3, h4, hneg, hpos⟩

/-! ## The arithmetic anchor factor -/

/-- **(PI7)** For the Boolean avoidance coordinate the common-anchor factor is the indicator that
every anchor prime hits at least one of the two source indices. -/
theorem commonAnchorWeight_avoidCoordinate (C : Finset ℕ) (m n : ℕ) :
    commonAnchorWeight C avoidCoordinate m n =
      if ∀ p ∈ C, p ∣ m ∨ p ∣ n then 1 else 0 := by
  classical
  induction C using Finset.induction with
  | empty => simp [commonAnchorWeight]
  | insert q C hq ih =>
      rw [commonAnchorWeight, Finset.prod_insert hq, ← commonAnchorWeight, ih]
      by_cases hqm : q ∣ m
      · by_cases hrest : ∀ p ∈ C, p ∣ m ∨ p ∣ n
        · rw [if_pos hrest, if_pos ?_]
          · simp [avoidCoordinate, hqm]
          · intro p hp
            rcases Finset.mem_insert.mp hp with h | h
            · exact Or.inl (h ▸ hqm)
            · exact hrest p h
        · rw [if_neg hrest, if_neg ?_]
          · ring
          · intro hall
            exact hrest fun p hp => hall p (Finset.mem_insert_of_mem hp)
      · by_cases hqn : q ∣ n
        · by_cases hrest : ∀ p ∈ C, p ∣ m ∨ p ∣ n
          · rw [if_pos hrest, if_pos ?_]
            · simp [avoidCoordinate, hqn]
            · intro p hp
              rcases Finset.mem_insert.mp hp with h | h
              · exact Or.inr (h ▸ hqn)
              · exact hrest p h
          · rw [if_neg hrest, if_neg ?_]
            · ring
            · intro hall
              exact hrest fun p hp => hall p (Finset.mem_insert_of_mem hp)
        · have hnot : ¬ ∀ p ∈ insert q C, p ∣ m ∨ p ∣ n := by
            intro hall
            rcases hall q (Finset.mem_insert_self q C) with h | h
            · exact hqm h
            · exact hqn h
          rw [if_neg hnot]
          simp [avoidCoordinate, hqm, hqn]

/-- For a finite set of primes the anchor factor is the indicator of divisibility of the product
of the two source indices by the anchor radical. -/
theorem commonAnchorWeight_avoidCoordinate_prime (C : Finset ℕ)
    (hC : ∀ p ∈ C, Nat.Prime p) (m n : ℕ) :
    commonAnchorWeight C avoidCoordinate m n =
      if (∏ p ∈ C, p) ∣ m * n then 1 else 0 := by
  rw [commonAnchorWeight_avoidCoordinate]
  by_cases h : ∀ p ∈ C, p ∣ m ∨ p ∣ n
  · have hdvd : (∏ p ∈ C, p) ∣ m * n :=
      Finset.prod_primes_dvd _ (fun p hp => (hC p hp).prime)
        fun p hp => ((hC p hp).dvd_mul).mpr (h p hp)
    rw [if_pos h, if_pos hdvd]
  · have hnot : ¬ (∏ p ∈ C, p) ∣ m * n := by
      intro hdvd
      exact h fun p hp =>
        ((hC p hp).dvd_mul).mp (dvd_trans (Finset.dvd_prod_of_mem _ hp) hdvd)
    rw [if_neg h, if_neg hnot]

/-! ## Capstone -/

/-- **Physical interval-anchor coarea and aperture phase law.**  For every base and anchor of the
physical Boolean sieve, the anchor curvature of the centered clipped-interval packet energy is an
exact difference of two nonnegative masses, the anchored Boolean-cover overlap mass and the
anchored rank-one centering mass; and the complete two-atom physical packet realizes both
curvature signs, with exactly one transition aperture strictly between `3c` and `4c`. -/
theorem physical_interval_anchor_coarea_phase_law :
    (∀ (A : ℝ) (indices : Finset ℕ) (base anchor : Finset ℕ), Disjoint base anchor →
        ∀ lo hi : ℕ → ℝ,
        (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
            physicalEnergy A indices (base ∪ d) avoidCoordinate physWeight lo hi) =
          anchorCoareaMass A indices base anchor avoidCoordinate physWeight lo hi -
            anchorCenteringMass A indices base anchor avoidCoordinate physWeight lo hi / A) ∧
      (∀ (A : ℝ) (indices : Finset ℕ) (base anchor : Finset ℕ) (lo hi : ℕ → ℝ),
        0 ≤ anchorCoareaMass A indices base anchor avoidCoordinate physWeight lo hi ∧
          0 ≤ anchorCenteringMass A indices base anchor avoidCoordinate physWeight lo hi) ∧
      3 * physCellWidth < physTransitionAperture ∧
        physTransitionAperture < 4 * physCellWidth ∧
      (∀ A : ℝ, Real.log 2 ≤ A →
        ((∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
            physicalEnergy A physAtoms (∅ ∪ d) avoidCoordinate physWeight physLo physHi) < 0 ↔
          A < physTransitionAperture)) ∧
      (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy (3 * physCellWidth) physAtoms (∅ ∪ d) avoidCoordinate physWeight
          physLo physHi) < 0 ∧
      0 < (∑ d ∈ ({2} : Finset ℕ).powerset, (-1 : ℝ) ^ d.card *
        physicalEnergy (4 * physCellWidth) physAtoms (∅ ∪ d) avoidCoordinate physWeight
          physLo physHi) := by
  obtain ⟨hlo, hhi⟩ := physTransitionAperture_mem_Ioo
  obtain ⟨_, _, hneg, hpos⟩ := physicalTwoPrimeCurvature_sign_witnesses
  refine ⟨fun A indices base anchor hdisj lo hi =>
      physicalAnchorCurvature_eq A indices base anchor hdisj avoidCoordinate physWeight lo hi,
    fun A indices base anchor lo hi =>
      ⟨anchorCoareaMass_nonneg A indices base anchor avoidCoordinate physWeight lo hi
        avoidCoordinate_zero_or_one physWeight_nonneg,
       anchorCenteringMass_nonneg A indices base anchor avoidCoordinate physWeight lo hi
        avoidCoordinate_zero_or_one physWeight_nonneg⟩,
    hlo, hhi, fun A hA => (physicalTwoPrimeCurvature_phase_law hA).1, hneg, hpos⟩

end

end PhysicalAnchor

end RHTower
