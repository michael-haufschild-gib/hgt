import GaloisForLFunctions.HTGeometry.FacePacketDisplacementFreeness
import GaloisForLFunctions.HTGeometry.FacePacketLayerGluing
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaBottomFace
import GaloisForLFunctions.HTGeometry.EllipticGammaMixedFace

/-!
# The face with one surviving parameter is a translated theta logarithmic derivative

Deleting one more parameter from a face with two survivors is the coface difference of the
order-one elliptic gamma, and that difference is the Jacobi theta logarithmic derivative up to a
translation and an additive constant.  So a face with exactly one surviving parameter carries the
theta coordinate, and its translation stabilizer is the theta lattice.

* **`multipleEllipticGammaLogDerivFaceMero_one_surviving`** — the identification;
* **`exists_lattice_of_fix_one_surviving`** — a translation fixing such a face lies in `ℤ + ℤτ`;
* `faceShiftLattice_eq_zero_of_theta_lattice` — an external lattice vector of that shape vanishes;
* **`facePacketDisplacementSlice_injective_one_surviving`** — freeness of the displacement
  labelling when the deeper face keeps exactly one parameter;
* **`not_facePacketDisplacementSlice_injective_of_terminal`** — and its failure when the deeper
  face keeps none.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry
open MatroidGluing MatroidGluing.Rank MatroidGluing.Meromorphic

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The identification -/

/-- **A face with exactly one surviving parameter carries a translated theta logarithmic
derivative.**  Removing a deleted parameter from the face exhibits it as the coface difference of
the order-one elliptic gamma, which is the theta coordinate up to a constant. -/
theorem multipleEllipticGammaLogDerivFaceMero_one_surviving
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (L : Finset ι) {a b : ι}
    (haL : a ∈ L) (hbL : b ∉ L) (hL : ∀ i, i ∉ L → i = b) :
    ∃ c : ℂ,
      multipleEllipticGammaLogDerivFaceMero τ hτ L =
        addTranslationMeroEquiv (-(1 + τ b) / 2) (thetaLogDerivMero (τ b) (hτ b)) +
          algebraMap (analyticSubring Set.univ) (meroField Set.univ)
            (constToAnalytic Set.univ c) := by
  classical
  have haL' : a ∉ L.erase a := by simp
  have hbL' : b ∉ L.erase a := fun hmem => hbL (Finset.mem_of_mem_erase hmem)
  have hab : a ≠ b := fun hh => hbL (hh ▸ haL)
  have hsurv : ∀ i, i ∉ L.erase a → i = a ∨ i = b := by
    intro i hi
    by_cases hia : i = a
    · exact Or.inl hia
    · exact Or.inr (hL i fun hiL => hi (Finset.mem_erase.mpr ⟨hia, hiL⟩))
  obtain ⟨c, hface⟩ := ellipticGammaLogDerivMero_source_face_sigma (hτ a) (hτ b)
  refine ⟨c, ?_⟩
  have hcoface :=
    multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ (L.erase a) a haL'
  rw [Finset.insert_erase haL] at hcoface
  rw [← hcoface,
    multipleEllipticGammaLogDerivFaceMero_two_surviving τ hτ (L.erase a) haL' hbL' hab hsurv]
  have hcomm : addTranslationMeroEquiv (τ a)
        (addTranslationMeroEquiv (-(1 + τ b) / 2)
          (ellipticGammaLogDerivMero (τ a) (τ b) (hτ a) (hτ b))) =
      addTranslationMeroEquiv (-(1 + τ b) / 2)
        (addTranslationMeroEquiv (τ a)
          (ellipticGammaLogDerivMero (τ a) (τ b) (hτ a) (hτ b))) := by
    rw [addTranslationMeroEquiv_add, addTranslationMeroEquiv_add, add_comm]
  rw [hcomm, ← map_sub, hface, map_add, addTranslationMeroEquiv_const]

/-! ## The stabilizer of such a face -/

set_option synthInstance.maxHeartbeats 800000 in
/-- **A translation fixing a face with one surviving parameter lies in the theta lattice of that
parameter.**  The face is a translate of the theta coordinate up to a constant, so a fixing
translation makes the theta defect vanish, which forces a lattice shift. -/
theorem exists_lattice_of_fix_one_surviving
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (L : Finset ι) {a b : ι}
    (haL : a ∈ L) (hbL : b ∉ L) (hL : ∀ i, i ∉ L → i = b) {h : ℂ}
    (hfix : addTranslationMeroEquiv h (multipleEllipticGammaLogDerivFaceMero τ hτ L) =
      multipleEllipticGammaLogDerivFaceMero τ hτ L) :
    ∃ m n : ℤ, h = (m : ℂ) + (n : ℂ) * τ b := by
  classical
  obtain ⟨c, hform⟩ :=
    multipleEllipticGammaLogDerivFaceMero_one_surviving τ hτ L haL hbL hL
  rw [hform, map_add, addTranslationMeroEquiv_const, addTranslationMeroEquiv_add,
    add_comm h (-(1 + τ b) / 2), ← addTranslationMeroEquiv_add] at hfix
  have hstep : addTranslationMeroEquiv (-(1 + τ b) / 2)
        (addTranslationMeroEquiv h (thetaLogDerivMero (τ b) (hτ b))) =
      addTranslationMeroEquiv (-(1 + τ b) / 2) (thetaLogDerivMero (τ b) (hτ b)) :=
    add_right_cancel hfix
  have htheta : addTranslationMeroEquiv h (thetaLogDerivMero (τ b) (hτ b)) =
      thetaLogDerivMero (τ b) (hτ b) :=
    (addTranslationMeroEquiv (-(1 + τ b) / 2)).injective hstep
  by_contra hcon
  exact thetaLogDerivDefectMero_ne_zero_of_nonlattice (h := h) (hτ b) hcon
    (by rw [thetaLogDerivDefectMero, htheta, sub_self])

/-! ## Clearing an external lattice vector against the theta lattice -/

omit [DecidableEq ι] in
/-- An external lattice vector of a face that is also a theta lattice vector of a parameter deleted
by no member of the face vanishes: the two presentations form an integral relation with the unit
period. -/
theorem faceShiftLattice_eq_zero_of_theta_lattice
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ) (J : Finset ι) {r : ι} (hr : r ∉ J)
    {h : ℂ} (hmem : h ∈ faceShiftLattice τ J) {m n : ℤ}
    (hmn : h = (m : ℂ) + (n : ℂ) * τ r) :
    h = 0 := by
  classical
  obtain ⟨N, hN, hsum⟩ := hmem
  have hterm : ∀ j : ι, ((N j - (if j = r then n else 0) : ℤ) : ℂ) * τ j =
      ((N j : ℤ) : ℂ) * τ j - (if j = r then (n : ℂ) * τ j else 0) := by
    intro j
    by_cases hj : j = r
    · subst hj
      simp
      ring
    · simp [hj]
  have hsum2 : ∑ j, ((N j - (if j = r then n else 0) : ℤ) : ℂ) * τ j =
      (∑ j, ((N j : ℤ) : ℂ) * τ j) - (n : ℂ) * τ r := by
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ r fun j => (n : ℂ) * τ j]
    simp
  have hrel : ((-m : ℤ) : ℂ) +
      ∑ j, ((N j - (if j = r then n else 0) : ℤ) : ℂ) * τ j = 0 := by
    rw [hsum2, ← hsum]
    push_cast
    linear_combination hmn
  obtain ⟨hm0, hall⟩ := hQ (-m) (fun j => N j - (if j = r then n else 0)) hrel
  have hkr : N r - n = 0 := by simpa using hall r
  have hNr : N r = 0 := hN r hr
  have hm : m = 0 := by omega
  have hn : n = 0 := by omega
  rw [hmn, hm, hn]
  simp

/-! ## The two extreme faces -/

/-- **Freeness of the displacement labelling when the deeper face keeps exactly one parameter.**
The deeper face is a translated theta coordinate, so a fixing external shift lies in the theta
lattice of the surviving parameter; integral independence then forces it to vanish. -/
theorem facePacketDisplacementSlice_injective_one_surviving
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J : Finset ι) {q : ι} (hq : q ∉ J) {r : ι} (hr : r ∉ insert q J)
    (hunique : ∀ i, i ∉ insert q J → i = r) :
    Function.Injective (facePacketDisplacementSlice τ hτ J hq) := by
  refine facePacketDisplacementSlice_injective_of_period τ hτ J hq ?_
  intro h hmem hfix
  have hrJ : r ∉ J := fun hh => hr (Finset.mem_insert_of_mem hh)
  obtain ⟨m, n, hmn⟩ :=
    exists_lattice_of_fix_one_surviving τ hτ (insert q J)
      (Finset.mem_insert_self q J) hr hunique hfix
  have hzero : h = 0 := faceShiftLattice_eq_zero_of_theta_lattice τ hQ J hrJ hmem hmn
  rw [hzero, addTranslationMeroEquiv_zero_apply]

/-- **The freeness hypothesis fails at the terminal face.**  With no parameter surviving the deeper
face, freeness would force every external shift to fix the face coordinate; but that coordinate is a
translated theta coordinate of the single surviving parameter, and no nonzero external shift lies in
its lattice. -/
theorem not_facePacketDisplacementSlice_injective_of_terminal
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J : Finset ι) {q : ι} (hq : q ∉ J) (hfull : insert q J = (Finset.univ : Finset ι))
    (hJ : J.Nonempty) :
    ¬ Function.Injective (facePacketDisplacementSlice τ hτ J hq) := by
  classical
  intro hinj
  obtain ⟨a, haJ⟩ := hJ
  have hunique : ∀ i, i ∉ J → i = q := by
    intro i hi
    by_contra hiq
    have : i ∈ insert q J := by rw [hfull]; exact Finset.mem_univ i
    rcases Finset.mem_insert.mp this with h | h
    · exact hiq h
    · exact hi h
  have hmem : τ a ∈ faceShiftLattice τ J := by
    refine ⟨fun i => if i = a then 1 else 0, ?_, ?_⟩
    · intro i hi
      have hia : i ≠ a := fun hh => hi (hh ▸ haJ)
      simp [hia]
    · rw [Finset.sum_congr rfl fun j _ =>
        (by by_cases hj : j = a <;> simp [hj] :
          (((if j = a then 1 else 0 : ℤ)) : ℂ) * τ j = if j = a then τ j else 0),
        Finset.sum_ite_eq' Finset.univ a fun j => τ j]
      simp
  have hfix := ((facePacketDisplacementSlice_injective_iff_period_of_terminal
    τ hτ J hq hfull).mp hinj) (τ a) hmem
  obtain ⟨m, n, hmn⟩ :=
    exists_lattice_of_fix_one_surviving τ hτ J haJ hq hunique hfix
  have hzero : τ a = 0 :=
    faceShiftLattice_eq_zero_of_theta_lattice τ hQ J hq hmem hmn
  have := hτ a
  rw [hzero] at this
  simp at this

/-! ## The complete classification -/

omit [DecidableEq ι] in
/-- The external lattice of the empty face is trivial. -/
theorem faceShiftLattice_empty (τ : ι → ℂ) {h : ℂ}
    (hmem : h ∈ faceShiftLattice τ (∅ : Finset ι)) : h = 0 := by
  obtain ⟨N, hN, rfl⟩ := hmem
  have hzero : ∀ i, N i = 0 := fun i => hN i (by simp)
  simp [hzero]

/-- **Exact criterion for freeness of the displacement labelling.**  For an integrally independent
period family the labelling is injective precisely when the deeper face still keeps a parameter, the
only exception being the empty face, whose packet is a single germ.  The three regimes of the
trichotomy are the three ways this criterion is met or missed. -/
theorem facePacketDisplacementSlice_injective_iff
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    (J : Finset ι) {q : ι} (hq : q ∉ J) :
    Function.Injective (facePacketDisplacementSlice τ hτ J hq) ↔
      insert q J ≠ (Finset.univ : Finset ι) ∨ J = (∅ : Finset ι) := by
  classical
  constructor
  · intro hinj
    by_cases hfull : insert q J = (Finset.univ : Finset ι)
    · right
      by_contra hJne
      exact not_facePacketDisplacementSlice_injective_of_terminal τ hτ hQ J hq hfull
        (Finset.nonempty_iff_ne_empty.mpr hJne) hinj
    · exact Or.inl hfull
  · rintro (hne | rfl)
    · have hne' : ((insert q J)ᶜ).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hh
        exact hne ((Finset.compl_eq_empty_iff (insert q J)).mp hh)
      have hpos : 0 < ((insert q J)ᶜ).card := Finset.card_pos.mpr hne'
      rcases Nat.lt_or_ge ((insert q J)ᶜ).card 2 with hlt | h2
      · obtain ⟨r, hrset⟩ := Finset.card_eq_one.mp (by omega : ((insert q J)ᶜ).card = 1)
        have hr : r ∉ insert q J := by
          have : r ∈ ((insert q J)ᶜ) := by rw [hrset]; exact Finset.mem_singleton_self r
          exact Finset.mem_compl.mp this
        have hunique : ∀ i, i ∉ insert q J → i = r := by
          intro i hi
          have : i ∈ ((insert q J)ᶜ) := Finset.mem_compl.mpr hi
          rw [hrset] at this
          exact Finset.mem_singleton.mp this
        exact facePacketDisplacementSlice_injective_one_surviving τ hτ hQ J hq hr hunique
      · exact facePacketDisplacementSlice_injective τ hτ hQ J hq h2
    · refine facePacketDisplacementSlice_injective_of_period τ hτ _ hq ?_
      intro h hmem _
      rw [faceShiftLattice_empty τ hmem, addTranslationMeroEquiv_zero_apply]

/-! ## The descending face-lifting lemma without its freeness and period premises -/

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

set_option synthInstance.maxHeartbeats 800000 in
/-- **Descending face-lifting with only its inductive premise left.**  For an integrally
independent period family and a face whose deeper coface is not terminal, both the rational
independence of the three periods and the freeness of the displacement labelling are automatic, so
the translation block is differentially independent as soon as the target packet is independent over
the complementary base. -/
theorem facePacket_differentialIndependent_of_periodsIntegrallyIndependent
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (J : Finset ι) {q u : ι} (hqJ : q ∉ J) (huJ : u ∉ J) (hqu : q ≠ u)
    (hqS : insert q J ∈ S) (huS : insert u J ∈ S) (hJS : J ∉ S)
    (hne : insert q J ≠ (Finset.univ : Finset ι))
    (hindep : DifferentialIndependent
      ↥(differentialAdjoin ℂ (facePacketUnion τ hτ (facePacketBaseFamily S J q)))
      (facePalette τ hτ (insert q J) q)) :
    DifferentialIndependent ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
      (facePacketBlock τ hτ J) :=
  facePacket_differentialIndependent_of_free τ hτ hS J hqJ huJ hqS huS hJS
    (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ hqu)
    hindep
    ((facePacketDisplacementSlice_injective_iff τ hτ hQ J hqJ).mpr (Or.inl hne))

set_option synthInstance.maxHeartbeats 800000 in
/-- **One face layer, with its arithmetic premises discharged.**  For an integrally independent
period family whose chosen surviving directions are distinct and keep the next face nonterminal,
the rational independence of the three periods and the freeness of every displacement labelling are
automatic, so the layer is jointly independent over the deeper face field as soon as the analytic
star inputs hold. -/
theorem multipleEllipticGammaFaceLayer_diffIndepOn_deeper_of_periodsIntegrallyIndependent
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (hQ : PeriodsIntegrallyIndependent τ)
    {S : Set (Finset ι)} (hS : ∀ L ∈ S, ∀ p : ι, p ∉ L → insert p L ∈ S)
    (faces : Finset (Finset ι)) (s : ℕ)
    (huniform : ∀ J ∈ faces, J.card = s)
    (dq du : Finset ι → ι)
    (hq : ∀ J ∈ faces, dq J ∉ J) (hu : ∀ J ∈ faces, du J ∉ J)
    (hqu : ∀ J ∈ faces, dq J ≠ du J)
    (hqS : ∀ J ∈ faces, insert (dq J) J ∈ S) (huS : ∀ J ∈ faces, insert (du J) J ∈ S)
    (hJS : ∀ J ∈ faces, J ∉ S)
    (hne : ∀ J ∈ faces, insert (dq J) J ≠ (Finset.univ : Finset ι))
    (hfree : ∀ J ∈ faces, DifferentialIndependent
      ↥(differentialAdjoin ℂ (facePacketUnion τ hτ (facePacketBaseFamily S J (dq J))))
      (facePalette τ hτ (insert (dq J) J) (dq J)))
    (hStarInj : ∀ (A : Finset ι) (q : ι), A.card < s → q ∉ A →
      ∀ (m n : ℤ) (y z : meroField (Set.univ : Set ℂ)),
        y ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) →
        z ∈ (⋃ J ∈ faces.filter (fun J => insert q A ⊆ J),
          multipleEllipticGammaFacePacketSlice τ hτ J q) →
        (meroTranslationPerm (τ q) ^ m) y = (meroTranslationPerm (τ q) ^ n) z → m = n)
    (hOffDA : ∀ (A : Finset ι) (q : ι), A.card < s → q ∉ A →
      ∀ t : Finset (meroField (Set.univ : Set ℂ)),
        (↑t : Set (meroField (Set.univ : Set ℂ))) ⊆
          (⋃ J ∈ (faces.filter (fun J => A ⊆ J)).filter (fun J => q ∉ J),
            multipleEllipticGammaFacePacket τ hτ J) →
        ∀ n : ℤ, ∀ z ∈ (⇑(meroTranslationPerm (τ q) ^ n)) ''
            (↑t : Set (meroField (Set.univ : Set ℂ))),
          DifferentialAlgebraicOver
            (differentialAdjoin ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
              (↑t : Set (meroField (Set.univ : Set ℂ)))) z) :
    DiffIndepOn ↥(differentialAdjoin ℂ (facePacketUnion τ hτ S))
      (faceStar faces (multipleEllipticGammaFacePacket τ hτ) ∅) :=
  multipleEllipticGammaFaceLayer_diffIndepOn_deeper τ hτ hS faces s huniform dq du hq hu
    hqS huS hJS
    (fun J hJ =>
      linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ (hqu J hJ))
    hfree
    (fun J hJ =>
      (facePacketDisplacementSlice_injective_iff τ hτ hQ J (hq J hJ)).mpr (Or.inl (hne J hJ)))
    hStarInj hOffDA

end

end GaloisForLFunctions
