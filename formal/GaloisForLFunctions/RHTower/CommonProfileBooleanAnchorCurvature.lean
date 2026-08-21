import GaloisForLFunctions.RHTower.PhysicalCutoffAliasResponseJoining
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Common-profile Boolean response and Gram anchor curvature

Two finite identities survive the failure of sectorwise response estimates.

First, a Bernoulli average of Boolean Möbius-transformed responses collapses exactly to the
corresponding signed occupancy response.  This is the abstract finite algebra behind the passage
from the anchored response `B_(c,r,h)` to the physical occupancy in `(AC24)`.

Second, when all sectors use one common Gram profile, the Boolean anchor occupancy is an exact
alternating finite difference of sifted Gram energies.  The theorem is proved for arbitrary real
coordinate weights; divisibility indicators are its Boolean specialization.  No sign or estimate
is asserted.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-! ## Bernoulli response collapse -/

/-- Boolean Möbius transform of a response packet.  The subset `d` is deleted from the active
packet `t`; this is the subset form of `B_r = sum_(d|r) mu(d) A_(r/d)`. -/
def booleanMobiusResponse {R : Type*} [CommRing R]
    (t : Finset ℕ) (response : Finset ℕ → R) : R :=
  ∑ d ∈ t.powerset, (-1 : R) ^ d.card * response (t \ d)

/-- Inserting one Boolean coordinate takes the difference between the response with that
coordinate retained and the original response. -/
theorem booleanMobiusResponse_insert {R : Type*} [CommRing R]
    {p : ℕ} {s : Finset ℕ} (hp : p ∉ s) (response : Finset ℕ → R) :
    booleanMobiusResponse (insert p s) response =
      booleanMobiusResponse s (fun t => response (insert p t)) -
        booleanMobiusResponse s response := by
  classical
  unfold booleanMobiusResponse
  rw [Finset.sum_powerset_insert hp, sub_eq_add_neg]
  congr 1
  · apply Finset.sum_congr rfl
    intro d hd
    have hpd : p ∉ d := fun hmem => hp ((Finset.mem_powerset.mp hd) hmem)
    have hdiff : insert p s \ d = insert p (s \ d) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    rw [hdiff]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hpd : p ∉ d := fun hmem => hp ((Finset.mem_powerset.mp hd) hmem)
    have hdiff : insert p s \ insert p d = s \ d := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    rw [hdiff, Finset.card_insert_of_notMem hpd, pow_succ]
    ring

/-- A coordinate absent from the active packet contributes its survival factor to the complete
Bernoulli weight. -/
theorem completeAliasWeight_insert_inactive {R : Type*} [CommRing R]
    {p : ℕ} {s t : Finset ℕ} (hp : p ∉ s) (ht : t ⊆ s) (θ : ℕ → R) :
    completeAliasWeight (insert p s) t θ =
      (1 - θ p) * completeAliasWeight s t θ := by
  classical
  have hpt : p ∉ t := fun hmem => hp (ht hmem)
  have hdiff : insert p s \ t = insert p (s \ t) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  have hpst : p ∉ s \ t := by simp [hp]
  unfold completeAliasWeight
  rw [hdiff, Finset.prod_insert hpst]
  ring

/-- A coordinate inserted into the active packet contributes its active Bernoulli factor. -/
theorem completeAliasWeight_insert_active {R : Type*} [CommRing R]
    {p : ℕ} {s t : Finset ℕ} (hp : p ∉ s) (ht : t ⊆ s) (θ : ℕ → R) :
    completeAliasWeight (insert p s) (insert p t) θ =
      θ p * completeAliasWeight s t θ := by
  classical
  have hpt : p ∉ t := fun hmem => hp (ht hmem)
  have hdiff : insert p s \ insert p t = s \ t := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    aesop
  unfold completeAliasWeight
  rw [Finset.prod_insert hpt, hdiff]
  ring

/-- Signed Bernoulli average of the Boolean Möbius responses. -/
def signedBernoulliMobiusResponse {R : Type*} [CommRing R]
    (s : Finset ℕ) (θ : ℕ → R) (response : Finset ℕ → R) : R :=
  ∑ t ∈ s.powerset,
    (-1 : R) ^ t.card * completeAliasWeight s t θ *
      booleanMobiusResponse t response

/-- The collapsed signed occupancy response. -/
def signedBernoulliResponse {R : Type*} [CommRing R]
    (s : Finset ℕ) (θ : ℕ → R) (response : Finset ℕ → R) : R :=
  ∑ t ∈ s.powerset,
    (-1 : R) ^ t.card * (∏ p ∈ t, θ p) * response t

/-- Inserting a Bernoulli coordinate in the Möbius-response average is a deletion-contraction
step on the underlying response packet. -/
theorem signedBernoulliMobiusResponse_insert {R : Type*} [CommRing R]
    {p : ℕ} {s : Finset ℕ} (hp : p ∉ s) (θ : ℕ → R)
    (response : Finset ℕ → R) :
    signedBernoulliMobiusResponse (insert p s) θ response =
      signedBernoulliMobiusResponse s θ response -
        θ p * signedBernoulliMobiusResponse s θ
          (fun t => response (insert p t)) := by
  classical
  unfold signedBernoulliMobiusResponse
  rw [Finset.sum_powerset_insert hp, ← Finset.sum_add_distrib]
  calc
    (∑ t ∈ s.powerset,
        ((-1 : R) ^ t.card * completeAliasWeight (insert p s) t θ *
              booleanMobiusResponse t response +
          (-1 : R) ^ (insert p t).card *
              completeAliasWeight (insert p s) (insert p t) θ *
                booleanMobiusResponse (insert p t) response)) =
        ∑ t ∈ s.powerset,
          (((-1 : R) ^ t.card * completeAliasWeight s t θ *
              booleanMobiusResponse t response) -
            θ p * ((-1 : R) ^ t.card * completeAliasWeight s t θ *
              booleanMobiusResponse t (fun u => response (insert p u)))) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hts : t ⊆ s := Finset.mem_powerset.mp ht
      have hpt : p ∉ t := fun hmem => hp (hts hmem)
      rw [completeAliasWeight_insert_inactive hp hts,
        completeAliasWeight_insert_active hp hts,
        booleanMobiusResponse_insert hpt response,
        Finset.card_insert_of_notMem hpt, pow_succ]
      ring
    _ =
        (∑ t ∈ s.powerset,
          (-1 : R) ^ t.card * completeAliasWeight s t θ *
            booleanMobiusResponse t response) -
          θ p *
            ∑ t ∈ s.powerset,
              (-1 : R) ^ t.card * completeAliasWeight s t θ *
                booleanMobiusResponse t (fun u => response (insert p u)) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The collapsed signed occupancy response obeys the same deletion-contraction recursion. -/
theorem signedBernoulliResponse_insert {R : Type*} [CommRing R]
    {p : ℕ} {s : Finset ℕ} (hp : p ∉ s) (θ : ℕ → R)
    (response : Finset ℕ → R) :
    signedBernoulliResponse (insert p s) θ response =
      signedBernoulliResponse s θ response -
        θ p * signedBernoulliResponse s θ (fun t => response (insert p t)) := by
  classical
  unfold signedBernoulliResponse
  rw [Finset.sum_powerset_insert hp, ← Finset.sum_add_distrib]
  calc
    (∑ t ∈ s.powerset,
        ((-1 : R) ^ t.card * (∏ q ∈ t, θ q) * response t +
          (-1 : R) ^ (insert p t).card *
            (∏ q ∈ insert p t, θ q) * response (insert p t))) =
        ∑ t ∈ s.powerset,
          (((-1 : R) ^ t.card * (∏ q ∈ t, θ q) * response t) -
            θ p * ((-1 : R) ^ t.card * (∏ q ∈ t, θ q) *
              response (insert p t))) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hts : t ⊆ s := Finset.mem_powerset.mp ht
      have hpt : p ∉ t := fun hmem => hp (hts hmem)
      rw [Finset.card_insert_of_notMem hpt, Finset.prod_insert hpt, pow_succ]
      ring
    _ =
        (∑ t ∈ s.powerset,
          (-1 : R) ^ t.card * (∏ q ∈ t, θ q) * response t) -
          θ p *
            ∑ t ∈ s.powerset,
              (-1 : R) ^ t.card * (∏ q ∈ t, θ q) *
                response (insert p t) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- **Response--occupancy identity.**  Averaging Boolean Möbius-transformed responses against the
complete active/survival Bernoulli law leaves exactly one signed active response per packet.
This is the finite algebra in `Eresp = sum_e mu(e) theta(e) A_e`. -/
theorem signedBernoulliMobiusResponse_eq_signedBernoulliResponse
    {R : Type*} [CommRing R]
    (s : Finset ℕ) (θ : ℕ → R) (response : Finset ℕ → R) :
    signedBernoulliMobiusResponse s θ response =
      signedBernoulliResponse s θ response := by
  classical
  induction s using Finset.induction_on generalizing response with
  | empty =>
      simp [signedBernoulliMobiusResponse, signedBernoulliResponse,
        booleanMobiusResponse, completeAliasWeight]
  | @insert p s hp ih =>
      rw [signedBernoulliMobiusResponse_insert hp θ response,
        signedBernoulliResponse_insert hp θ response,
        ih response, ih (fun t => response (insert p t))]

/-! ## Common-Gram Boolean anchor curvature -/

/-- Multiplicative weight of one coordinate packet at one source index. -/
def coordinatePacketWeight {ι κ : Type*}
    (s : Finset ι) (coordinate : ι → κ → ℝ) (x : κ) : ℝ :=
  ∏ p ∈ s, coordinate p x

/-- The common two-source anchor factor.  For Boolean avoidance coordinates this is the indicator
that every anchor coordinate hits at least one of the two source indices. -/
def commonAnchorWeight {ι κ : Type*}
    (anchor : Finset ι) (coordinate : ι → κ → ℝ) (x y : κ) : ℝ :=
  ∏ p ∈ anchor, (1 - coordinate p x * coordinate p y)

/-- Sifted state vector of a finite common profile. -/
def commonProfileSiftedVector {ι κ E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (indices : Finset κ) (s : Finset ι) (coordinate : ι → κ → ℝ)
    (g : κ → E) : E :=
  ∑ x ∈ indices, coordinatePacketWeight s coordinate x • g x

/-- Sifted Gram energy of the common profile. -/
def commonProfileSiftedEnergy {ι κ E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (indices : Finset κ) (s : Finset ι) (coordinate : ι → κ → ℝ)
    (g : κ → E) : ℝ :=
  ‖commonProfileSiftedVector indices s coordinate g‖ ^ 2

/-- Coordinate packet weights multiply over disjoint unions. -/
theorem coordinatePacketWeight_union {ι κ : Type*}
    [DecidableEq ι] {s t : Finset ι} (hst : Disjoint s t)
    (coordinate : ι → κ → ℝ) (x : κ) :
    coordinatePacketWeight (s ∪ t) coordinate x =
      coordinatePacketWeight s coordinate x * coordinatePacketWeight t coordinate x := by
  unfold coordinatePacketWeight
  exact Finset.prod_union hst

/-- Boolean inclusion-exclusion for the common two-source coordinate packet. -/
theorem sum_powerset_signed_commonCoordinateWeight {ι κ : Type*}
    [DecidableEq ι] (anchor : Finset ι) (coordinate : ι → κ → ℝ) (x y : κ) :
    (∑ d ∈ anchor.powerset,
      (-1 : ℝ) ^ d.card * coordinatePacketWeight d coordinate x *
        coordinatePacketWeight d coordinate y) =
      commonAnchorWeight anchor coordinate x y := by
  have hprod : ∀ d : Finset ι,
      coordinatePacketWeight d coordinate x * coordinatePacketWeight d coordinate y =
        ∏ p ∈ d, coordinate p x * coordinate p y := by
    intro d
    unfold coordinatePacketWeight
    rw [Finset.prod_mul_distrib]
  calc
    (∑ d ∈ anchor.powerset,
      (-1 : ℝ) ^ d.card * coordinatePacketWeight d coordinate x *
        coordinatePacketWeight d coordinate y) =
        ∑ d ∈ anchor.powerset,
          (-1 : ℝ) ^ d.card * ∏ p ∈ d, coordinate p x * coordinate p y := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [mul_assoc, hprod]
    _ = ∏ p ∈ anchor, (1 - coordinate p x * coordinate p y) := by
      simpa using
        (Finset.prod_sub (fun _ : ι => (1 : ℝ))
          (fun p => coordinate p x * coordinate p y) anchor).symm
    _ = commonAnchorWeight anchor coordinate x y := rfl

/-- Gram expansion of one sifted common-profile energy. -/
theorem commonProfileSiftedEnergy_eq_gram {ι κ E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (indices : Finset κ) (s : Finset ι) (coordinate : ι → κ → ℝ)
    (g : κ → E) :
    commonProfileSiftedEnergy indices s coordinate g =
      ∑ x ∈ indices, ∑ y ∈ indices,
        coordinatePacketWeight s coordinate x *
          coordinatePacketWeight s coordinate y * inner ℝ (g x) (g y) := by
  rw [commonProfileSiftedEnergy, ← real_inner_self_eq_norm_sq]
  unfold commonProfileSiftedVector
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro x _hx
  apply Finset.sum_congr rfl
  intro y _hy
  simp
  ring

/-- **Common-Gram Boolean anchor-curvature law.**  A common two-source anchor packet is exactly
the alternating finite difference of the sifted Gram energy.  The theorem allows arbitrary real
coordinate weights; zero-one divisibility avoidance is the arithmetic specialization. -/
theorem commonGramBooleanAnchorCurvature {ι κ E : Type*}
    [DecidableEq ι] [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (indices : Finset κ) (base anchor : Finset ι) (hdisj : Disjoint base anchor)
    (coordinate : ι → κ → ℝ) (g : κ → E) :
    (∑ x ∈ indices, ∑ y ∈ indices,
      coordinatePacketWeight base coordinate x *
        coordinatePacketWeight base coordinate y *
          commonAnchorWeight anchor coordinate x y * inner ℝ (g x) (g y)) =
      ∑ d ∈ anchor.powerset,
        (-1 : ℝ) ^ d.card *
          commonProfileSiftedEnergy indices (base ∪ d) coordinate g := by
  classical
  symm
  calc
    (∑ d ∈ anchor.powerset,
      (-1 : ℝ) ^ d.card *
        commonProfileSiftedEnergy indices (base ∪ d) coordinate g) =
        ∑ d ∈ anchor.powerset, ∑ x ∈ indices, ∑ y ∈ indices,
          (-1 : ℝ) ^ d.card *
            ((coordinatePacketWeight base coordinate x *
                coordinatePacketWeight d coordinate x) *
              (coordinatePacketWeight base coordinate y *
                coordinatePacketWeight d coordinate y) * inner ℝ (g x) (g y)) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdsub : d ⊆ anchor := Finset.mem_powerset.mp hd
      have hbd : Disjoint base d := by
        rw [Finset.disjoint_left]
        intro p hpbase hpd
        exact (Finset.disjoint_left.mp hdisj hpbase (hdsub hpd))
      rw [commonProfileSiftedEnergy_eq_gram, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      rw [coordinatePacketWeight_union hbd coordinate x,
        coordinatePacketWeight_union hbd coordinate y]
    _ = ∑ x ∈ indices, ∑ y ∈ indices, ∑ d ∈ anchor.powerset,
        (-1 : ℝ) ^ d.card *
          ((coordinatePacketWeight base coordinate x *
              coordinatePacketWeight d coordinate x) *
            (coordinatePacketWeight base coordinate y *
              coordinatePacketWeight d coordinate y) * inner ℝ (g x) (g y)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.sum_comm]
    _ = ∑ x ∈ indices, ∑ y ∈ indices,
        coordinatePacketWeight base coordinate x *
          coordinatePacketWeight base coordinate y *
            commonAnchorWeight anchor coordinate x y * inner ℝ (g x) (g y) := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← sum_powerset_signed_commonCoordinateWeight anchor coordinate x y,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _hd
      ring

/-! ## Sharp sign classification -/

/-- Two-pattern avoidance coordinate used by the rank-one universality witness.  Pattern `0`
survives every coordinate, while pattern `1` is deleted as soon as the packet is nonempty. -/
def rankOneCurvatureCoordinate {ι : Type*} (_p : ι) (i : Fin 2) : ℝ :=
  if i = 0 then 1 else 0

/-- Collinear two-pattern packet.  Its retained pattern has amplitude `t`; its deletable pattern
has amplitude one. -/
def rankOneCurvaturePacket (t : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then t else 1

/-- The retained rank-one pattern has coordinate weight one for every packet. -/
@[simp] theorem coordinatePacketWeight_rankOneCurvature_zero
    {ι : Type*} [DecidableEq ι] (s : Finset ι) :
    coordinatePacketWeight s rankOneCurvatureCoordinate (0 : Fin 2) = 1 := by
  simp [coordinatePacketWeight, rankOneCurvatureCoordinate]

/-- The deletable rank-one pattern has coordinate weight zero on every nonempty packet. -/
theorem coordinatePacketWeight_rankOneCurvature_one_of_nonempty
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.Nonempty) :
    coordinatePacketWeight s rankOneCurvatureCoordinate (1 : Fin 2) = 0 := by
  rcases hs with ⟨p, hp⟩
  unfold coordinatePacketWeight
  apply Finset.prod_eq_zero hp
  simp [rankOneCurvatureCoordinate]

/-- At the empty packet both collinear source patterns survive. -/
theorem commonProfileSiftedEnergy_rankOneCurvature_empty
    {ι : Type*} [DecidableEq ι] (t : ℝ) :
    commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) (∅ : Finset ι)
        rankOneCurvatureCoordinate (rankOneCurvaturePacket t) =
      (t + 1) ^ 2 := by
  simp [commonProfileSiftedEnergy, commonProfileSiftedVector,
    coordinatePacketWeight, rankOneCurvatureCoordinate, rankOneCurvaturePacket,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Every nonempty coordinate packet deletes the unit pattern and retains only amplitude `t`. -/
theorem commonProfileSiftedEnergy_rankOneCurvature_of_nonempty
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.Nonempty) (t : ℝ) :
    commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) s
        rankOneCurvatureCoordinate (rankOneCurvaturePacket t) =
      t ^ 2 := by
  have hzero := coordinatePacketWeight_rankOneCurvature_one_of_nonempty hs
  simp [commonProfileSiftedEnergy, commonProfileSiftedVector,
    coordinatePacketWeight_rankOneCurvature_zero, hzero,
    rankOneCurvaturePacket, Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Alternating Boolean curvature of the explicit one-dimensional two-pattern packet. -/
def rankOneCommonGramCurvature {ι : Type*} [DecidableEq ι]
    (anchor : Finset ι) (t : ℝ) : ℝ :=
  ∑ d ∈ anchor.powerset,
    (-1 : ℝ) ^ d.card *
      commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) d
        rankOneCurvatureCoordinate (rankOneCurvaturePacket t)

/-- The signed Boolean powerset mass vanishes for every nonempty coordinate packet. -/
theorem sum_powerset_neg_one_pow_eq_zero_of_nonempty
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.Nonempty) :
    (∑ d ∈ s.powerset, (-1 : ℝ) ^ d.card) = 0 := by
  calc
    (∑ d ∈ s.powerset, (-1 : ℝ) ^ d.card) =
        ∏ p ∈ s, ((1 : ℝ) - 1) := by
      simpa using
        (Finset.prod_sub (fun _ : ι => (1 : ℝ)) (fun _ => (1 : ℝ)) s).symm
    _ = 0 := by
      rcases hs with ⟨p, hp⟩
      apply Finset.prod_eq_zero hp
      ring

/-- **Rank-one curvature formula.**  Every nonempty Boolean anchor already has the affine
one-dimensional curvature family `1 + 2t`. -/
theorem rankOneCommonGramCurvature_eq_one_add_two_mul
    {ι : Type*} [DecidableEq ι] {anchor : Finset ι}
    (hanchor : anchor.Nonempty) (t : ℝ) :
    rankOneCommonGramCurvature anchor t = 1 + 2 * t := by
  let P := anchor.powerset
  have hempty : (∅ : Finset ι) ∈ P := by
    simp [P]
  have hsum : (∑ d ∈ P, (-1 : ℝ) ^ d.card) = 0 := by
    simpa [P] using sum_powerset_neg_one_pow_eq_zero_of_nonempty hanchor
  have htail : (∑ d ∈ P \ {∅}, (-1 : ℝ) ^ d.card) = -1 := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hempty] at hsum
    simp only [Finset.card_empty, pow_zero] at hsum
    linarith
  rw [rankOneCommonGramCurvature]
  change (∑ d ∈ P,
    (-1 : ℝ) ^ d.card *
      commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) d
        rankOneCurvatureCoordinate (rankOneCurvaturePacket t)) = 1 + 2 * t
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hempty]
  rw [commonProfileSiftedEnergy_rankOneCurvature_empty]
  simp only [Finset.card_empty, pow_zero, one_mul]
  have htailEnergy :
      (∑ d ∈ P \ {∅},
        (-1 : ℝ) ^ d.card *
          commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) d
            rankOneCurvatureCoordinate (rankOneCurvaturePacket t)) =
        (∑ d ∈ P \ {∅}, (-1 : ℝ) ^ d.card) * t ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have hdP : d ∈ P := (Finset.mem_sdiff.mp hd).1
    have hdne : d ≠ ∅ := by
      simpa using (Finset.mem_sdiff.mp hd).2
    have hdnonempty : d.Nonempty := Finset.nonempty_iff_ne_empty.mpr hdne
    rw [commonProfileSiftedEnergy_rankOneCurvature_of_nonempty hdnonempty]
  rw [htailEnergy, htail]
  ring

/-- With no anchor coordinate, curvature is just one squared norm and is therefore nonnegative. -/
theorem emptyAnchorCommonGramCurvature_nonneg {ι κ E : Type*}
    [DecidableEq ι] [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (indices : Finset κ) (base : Finset ι) (coordinate : ι → κ → ℝ) (g : κ → E) :
    0 ≤ ∑ d ∈ (∅ : Finset ι).powerset,
      (-1 : ℝ) ^ d.card *
        commonProfileSiftedEnergy indices (base ∪ d) coordinate g := by
  simp [commonProfileSiftedEnergy]

/-- **Sharp nonempty-anchor universality.**  For every target real number, an explicit
one-dimensional common Gram packet on two source patterns has exactly that Boolean curvature.
Thus common-Gram positivity alone imposes no sign, monotonicity, or finite bound once the anchor
is nonempty. -/
theorem exists_rankOneCommonGramCurvature_eq
    {ι : Type*} [DecidableEq ι] {anchor : Finset ι}
    (hanchor : anchor.Nonempty) (y : ℝ) :
    ∃ coordinate : ι → Fin 2 → ℝ, ∃ g : Fin 2 → ℝ,
      (∑ d ∈ anchor.powerset,
        (-1 : ℝ) ^ d.card *
          commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) d coordinate g) = y := by
  refine ⟨rankOneCurvatureCoordinate, rankOneCurvaturePacket ((y - 1) / 2), ?_⟩
  change rankOneCommonGramCurvature anchor ((y - 1) / 2) = y
  rw [rankOneCommonGramCurvature_eq_one_add_two_mul hanchor]
  ring

/-! ## The sharp classification over an arbitrary disjoint base -/

/-- The two-pattern avoidance coordinate adapted to a base packet.  Pattern `0` survives every
coordinate; pattern `1` survives exactly the coordinates of the base. -/
def rankOneBaseCoordinate {ι : Type*} [DecidableEq ι] (base : Finset ι) (_p : ι) (i : Fin 2) : ℝ :=
  if i = 0 then 1 else (if _p ∈ base then 1 else 0)

@[simp] theorem coordinatePacketWeight_rankOneBase_zero
    {ι : Type*} [DecidableEq ι] (base s : Finset ι) :
    coordinatePacketWeight s (rankOneBaseCoordinate base) (0 : Fin 2) = 1 := by
  simp [coordinatePacketWeight, rankOneBaseCoordinate]

theorem coordinatePacketWeight_rankOneBase_one_of_subset
    {ι : Type*} [DecidableEq ι] {base s : Finset ι} (hs : s ⊆ base) :
    coordinatePacketWeight s (rankOneBaseCoordinate base) (1 : Fin 2) = 1 := by
  unfold coordinatePacketWeight
  refine Finset.prod_eq_one fun p hp => ?_
  simp [rankOneBaseCoordinate, hs hp]

theorem coordinatePacketWeight_rankOneBase_one_of_not_subset
    {ι : Type*} [DecidableEq ι] {base s : Finset ι} (hs : ¬ s ⊆ base) :
    coordinatePacketWeight s (rankOneBaseCoordinate base) (1 : Fin 2) = 0 := by
  obtain ⟨p, hp, hpb⟩ := Finset.not_subset.mp hs
  unfold coordinatePacketWeight
  refine Finset.prod_eq_zero hp ?_
  simp [rankOneBaseCoordinate, hpb]

theorem commonProfileSiftedEnergy_rankOneBase_of_subset
    {ι : Type*} [DecidableEq ι] {base s : Finset ι} (hs : s ⊆ base) (t : ℝ) :
    commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) s
        (rankOneBaseCoordinate base) (rankOneCurvaturePacket t) = (t + 1) ^ 2 := by
  have hone := coordinatePacketWeight_rankOneBase_one_of_subset hs
  simp [commonProfileSiftedEnergy, commonProfileSiftedVector,
    coordinatePacketWeight_rankOneBase_zero, hone, rankOneCurvaturePacket,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem commonProfileSiftedEnergy_rankOneBase_of_not_subset
    {ι : Type*} [DecidableEq ι] {base s : Finset ι} (hs : ¬ s ⊆ base) (t : ℝ) :
    commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) s
        (rankOneBaseCoordinate base) (rankOneCurvaturePacket t) = t ^ 2 := by
  have hzero := coordinatePacketWeight_rankOneBase_one_of_not_subset hs
  simp [commonProfileSiftedEnergy, commonProfileSiftedVector,
    coordinatePacketWeight_rankOneBase_zero, hzero, rankOneCurvaturePacket,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- **Equation `(CG12)` over an arbitrary base.**  The alternating anchor curvature of the
explicit one-dimensional two-pattern packet is the affine family `1 + 2t`, for every base packet
disjoint from the anchor. -/
theorem rankOneBaseCurvature_eq_one_add_two_mul
    {ι : Type*} [DecidableEq ι] {base anchor : Finset ι} (hdisj : Disjoint base anchor)
    (hanchor : anchor.Nonempty) (t : ℝ) :
    (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
      commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) (base ∪ d)
        (rankOneBaseCoordinate base) (rankOneCurvaturePacket t)) = 1 + 2 * t := by
  classical
  set P := anchor.powerset with hP
  have hempty : (∅ : Finset ι) ∈ P := by simp [hP]
  have hsum : (∑ d ∈ P, (-1 : ℝ) ^ d.card) = 0 := by
    simpa [hP] using sum_powerset_neg_one_pow_eq_zero_of_nonempty hanchor
  have htail : (∑ d ∈ P \ {∅}, (-1 : ℝ) ^ d.card) = -1 := by
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hempty] at hsum
    simp only [Finset.card_empty, pow_zero] at hsum
    linarith
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hempty]
  have hbase : commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) (base ∪ ∅)
      (rankOneBaseCoordinate base) (rankOneCurvaturePacket t) = (t + 1) ^ 2 := by
    rw [Finset.union_empty]
    exact commonProfileSiftedEnergy_rankOneBase_of_subset (le_refl base) t
  rw [hbase]
  simp only [Finset.card_empty, pow_zero, one_mul]
  have htailEnergy :
      (∑ d ∈ P \ {∅}, (-1 : ℝ) ^ d.card *
        commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) (base ∪ d)
          (rankOneBaseCoordinate base) (rankOneCurvaturePacket t))
        = (∑ d ∈ P \ {∅}, (-1 : ℝ) ^ d.card) * t ^ 2 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdP : d ∈ P := (Finset.mem_sdiff.mp hd).1
    have hdsub : d ⊆ anchor := by simpa [hP] using hdP
    have hdne : d ≠ ∅ := by simpa using (Finset.mem_sdiff.mp hd).2
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hdne
    have hnotsub : ¬ (base ∪ d) ⊆ base := by
      intro hsub
      have hpb : p ∈ base := hsub (Finset.mem_union_right _ hp)
      exact (Finset.disjoint_left.mp hdisj hpb) (hdsub hp)
    rw [commonProfileSiftedEnergy_rankOneBase_of_not_subset hnotsub]
  rw [htailEnergy, htail]
  ring

/-- **Sharp nonempty-anchor universality over an arbitrary disjoint base.**  Equation `(CG10)`:
for every target real number there is an explicit one-dimensional common Gram packet on two source
patterns whose Boolean anchor curvature above the base is exactly that number. -/
theorem exists_rankOneBaseCurvature_eq
    {ι : Type*} [DecidableEq ι] {base anchor : Finset ι} (hdisj : Disjoint base anchor)
    (hanchor : anchor.Nonempty) (y : ℝ) :
    ∃ coordinate : ι → Fin 2 → ℝ, ∃ g : Fin 2 → ℝ,
      (∑ d ∈ anchor.powerset, (-1 : ℝ) ^ d.card *
        commonProfileSiftedEnergy (Finset.univ : Finset (Fin 2)) (base ∪ d) coordinate g) = y := by
  refine ⟨rankOneBaseCoordinate base, rankOneCurvaturePacket ((y - 1) / 2), ?_⟩
  rw [rankOneBaseCurvature_eq_one_add_two_mul hdisj hanchor]
  ring


end RHTower
