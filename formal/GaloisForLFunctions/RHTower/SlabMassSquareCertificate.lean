import GaloisForLFunctions.RHTower.SlabTraceEdgeEstimate
import GaloisForLFunctions.RHTower.BoundedClockZeroTransfer

/-!
# The mass-square maximization certificate: `Q ≤ M²` and its RH consumer

The ninth slab module: the consumer layer of the `|tr|²` boundary object.  The
`Q`-face of the vertical-edge energy `F(h) = ∮ |tr|² ds` has Laurent germ
`h·F(h) → 2π Q` with `Q = ∑ m_w²` the fiber mass-square sum, against the total
mass `M = ∑ m_w`.  This module formalizes the certificate's algebraic core and
closes it into a hypothesis-free RH equivalence over the existing slab stack
(modules 5–8).

* §1 — pure algebra: for finitely many nonnegative masses, `∑ m_i² ≤ (∑ m_i)²`
  (`sum_sq_le_sq_sum`), strictly whenever two members carry nonzero mass
  (`sum_sq_lt_sq_sum_of_two`), with the exact equality case: `Q = M²` iff at
  most one member is nonzero (`sum_sq_eq_sq_sum_iff`).
* §2 — the fiber reading: `heightFiberMass` (`M`) and `heightFiberMassSquare`
  (`Q`) of the height fiber; `Q ≤ M²` unconditionally
  (`heightFiberMassSquare_le_sq`); since every fiber point carries positive
  mass, `Q = M²` iff the fiber is a single point
  (`heightFiberMassSquare_eq_sq_iff_subsingleton`), iff the fiber lies on the
  critical line (`heightFiberMassSquare_eq_sq_iff_im_eq_zero` — a single
  OFF-line point is impossible: its Schwarz mirror would split the fiber, by
  the module-7 line dichotomy `heightFiber_im_eq_zero_iff_subsingleton`), iff
  the fiber variance vanishes
  (`heightFiberMassSquare_eq_sq_iff_fiberVariance_eq_zero`).
* §3 — the fiber mirror symmetry with multiplicity: the Schwarz reflection
  `d ↦ −d` preserves packet masses (`xiPacketMass_conj`, from the corpus
  Schwarz reality `XiC_conj` and order equivariance
  `analyticOrderAt_conj_of_conjEquivariant`); packaged as
  `heightFiber_conj_mem_mass`.
* §4 — the consumers: `riemannHypothesis_iff_xiC_zero_im_eq_zero` (RH in the
  centered coordinate), `riemannHypothesis_iff_forall_heightFiber_im_eq_zero`,
  `riemannHypothesis_iff_forall_heightFiber_subsingleton`,
  `riemannHypothesis_iff_forall_fiberVariance_eq_zero`, and the capstone
  `riemannHypothesis_iff_forall_heightFiber_massSquare`: **RH ⟺ at every
  height the fiber mass-square identity `Q = M²` holds** — with its one-sided
  maximization form `riemannHypothesis_iff_forall_sq_le_heightFiberMassSquare`
  (`M² ≤ Q` suffices, since `Q ≤ M²` is unconditional).

Everything is hypothesis-free: the only inputs are the slab-stack fiber
machinery, the strip confinement `xiC_zero_im_mem_openHalf`, the corpus RH
coordinate bridges (`rh_iff_xi_ne_zero_right`,
`xiC_zero_im_eq_zero_of_riemannHypothesis`), and finite `Finset` algebra.
-/

open Complex Set Filter Topology

namespace RHTower
namespace SlabMassSquareCertificate

open SlabGermResidueTransport SlabFullWidthAdmissibility SlabConjugatedGermTheorem

noncomputable section

/-! ## §1 Pure algebra: the mass-square inequality and its equality case -/

/-- **The mass-square inequality.**  For a finite family of nonnegative masses the sum of
squares is at most the square of the total mass: every cross term of `M²` is nonnegative. -/
theorem sum_sq_le_sq_sum {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) :
    ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 := by
  have hstep : ∀ i ∈ s, m i ^ 2 ≤ m i * ∑ j ∈ s, m j := by
    intro i hi
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hm hi) (hm i hi)
  calc ∑ i ∈ s, m i ^ 2 ≤ ∑ i ∈ s, m i * ∑ j ∈ s, m j := Finset.sum_le_sum hstep
    _ = (∑ i ∈ s, m i) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- **Strictness under splitting.**  As soon as two distinct members carry nonzero mass the
mass-square inequality is strict: the `i`-th square loses against `m_i · M` because
`m_i < M`. -/
theorem sum_sq_lt_sq_sum_of_two {ι : Type*} {s : Finset ι} {m : ι → ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hmi : m i ≠ 0) (hmj : m j ≠ 0) :
    ∑ k ∈ s, m k ^ 2 < (∑ k ∈ s, m k) ^ 2 := by
  classical
  have hmi' : 0 < m i := lt_of_le_of_ne (hm i hi) (Ne.symm hmi)
  have hmj' : 0 < m j := lt_of_le_of_ne (hm j hj) (Ne.symm hmj)
  have hpair : m i + m j ≤ ∑ k ∈ s, m k := by
    have hsub : ({i, j} : Finset ι) ⊆ s := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hi
      · rw [Finset.mem_singleton] at hk
        subst hk
        exact hj
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hm k hk
    rwa [Finset.sum_pair hij] at h
  have hlt : m i < ∑ k ∈ s, m k := by linarith
  have hstep : ∀ k ∈ s, m k ^ 2 ≤ m k * ∑ l ∈ s, m l := by
    intro k hk
    rw [sq]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hm hk) (hm k hk)
  have hstrict : m i ^ 2 < m i * ∑ l ∈ s, m l := by
    rw [sq]
    exact mul_lt_mul_of_pos_left hlt hmi'
  calc ∑ k ∈ s, m k ^ 2 < ∑ k ∈ s, m k * ∑ l ∈ s, m l :=
      Finset.sum_lt_sum hstep ⟨i, hi, hstrict⟩
    _ = (∑ k ∈ s, m k) ^ 2 := by rw [← Finset.sum_mul, sq]

/-- **The exact equality case.**  `Q = M²` holds iff the family has at most one nonzero
member.  This is the algebraic heart of the maximization certificate: equality is
concentration. -/
theorem sum_sq_eq_sq_sum_iff {ι : Type*} {s : Finset ι} {m : ι → ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) :
    ∑ i ∈ s, m i ^ 2 = (∑ i ∈ s, m i) ^ 2 ↔
      ∀ i ∈ s, ∀ j ∈ s, m i ≠ 0 → m j ≠ 0 → i = j := by
  classical
  constructor
  · intro heq i hi j hj hmi hmj
    by_contra hij
    exact absurd heq (ne_of_lt (sum_sq_lt_sq_sum_of_two hm hi hj hij hmi hmj))
  · intro hone
    by_cases hall : ∀ i ∈ s, m i = 0
    · have h1 : ∑ i ∈ s, m i ^ 2 = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hall i hi]; ring
      have h2 : ∑ i ∈ s, m i = 0 := Finset.sum_eq_zero hall
      rw [h1, h2]
      ring
    · push Not at hall
      obtain ⟨i₀, hi₀, hmi₀⟩ := hall
      have hz : ∀ j ∈ s, j ≠ i₀ → m j = 0 := by
        intro j hj hne
        by_contra hmj
        exact hne (hone j hj i₀ hi₀ hmj hmi₀)
      have hM : ∑ k ∈ s, m k = m i₀ :=
        Finset.sum_eq_single i₀ hz fun h => absurd hi₀ h
      have hQ : ∑ k ∈ s, m k ^ 2 = m i₀ ^ 2 :=
        Finset.sum_eq_single i₀ (fun j hj hne => by rw [hz j hj hne]; ring)
          fun h => absurd hi₀ h
      rw [hM, hQ]

/-! ## §2 The fiber reading: `M`, `Q`, and the single-point characterizations -/

/-- The total multiplicity mass `M(γ)` of the height fiber. -/
def heightFiberMass (γ c : ℝ) : ℝ :=
  ∑ w ∈ heightFiber γ c, xiPacketMass w

/-- The mass-square sum `Q(γ)` of the height fiber — the `h⁻¹`-Laurent coefficient of the
vertical-edge energy `∮ |tr|² ds` up to the factor `2π`. -/
def heightFiberMassSquare (γ c : ℝ) : ℝ :=
  ∑ w ∈ heightFiber γ c, xiPacketMass w ^ 2

/-- Packet masses are nonnegative. -/
theorem xiPacketMass_nonneg (w : ℂ) : 0 ≤ xiPacketMass w := by
  unfold xiPacketMass
  exact Nat.cast_nonneg _

/-- **`Q ≤ M²` on the height fiber, unconditionally.**  The certificate's one-sided bound:
the mass-square sum never exceeds the squared total mass. -/
theorem heightFiberMassSquare_le_sq (γ c : ℝ) :
    heightFiberMassSquare γ c ≤ heightFiberMass γ c ^ 2 :=
  sum_sq_le_sq_sum _ _ fun w _ => xiPacketMass_nonneg w

/-- **`Q = M²` iff the fiber is a single point.**  Every fiber point carries positive mass,
so the algebraic equality case collapses to fiber subsingletonness. -/
theorem heightFiberMassSquare_eq_sq_iff_subsingleton {γ c : ℝ} (hc : 0 ≤ c) :
    heightFiberMassSquare γ c = heightFiberMass γ c ^ 2 ↔
      ∀ w ∈ heightFiber γ c, ∀ w' ∈ heightFiber γ c, w = w' := by
  unfold heightFiberMassSquare heightFiberMass
  rw [sum_sq_eq_sq_sum_iff fun w _ => xiPacketMass_nonneg w]
  constructor
  · intro hone w hw w' hw'
    exact hone w hw w' hw'
      (xiPacketMass_pos ((mem_heightFiber hc).mp hw).2.2).ne'
      (xiPacketMass_pos ((mem_heightFiber hc).mp hw').2.2).ne'
  · intro hpt w hw w' hw' _ _
    exact hpt w hw w' hw'

/-- **`Q = M²` reads the critical line.**  Equality holds iff the height fiber lies on the
critical line: a single OFF-line point is impossible, since its Schwarz mirror is a second
fiber point (the module-7 line dichotomy). -/
theorem heightFiberMassSquare_eq_sq_iff_im_eq_zero {γ c : ℝ} (hc : 0 ≤ c) :
    heightFiberMassSquare γ c = heightFiberMass γ c ^ 2 ↔
      ∀ w ∈ heightFiber γ c, w.im = 0 := by
  rw [heightFiberMassSquare_eq_sq_iff_subsingleton hc,
    ← heightFiber_im_eq_zero_iff_subsingleton hc]

/-- **`Q = M²` iff the fiber variance vanishes** — the glue to the module-7/8 displacement
certificate: the mass-square identity and the displacement-germ vanishing read the same
line. -/
theorem heightFiberMassSquare_eq_sq_iff_fiberVariance_eq_zero {γ c : ℝ} (hc : 0 ≤ c) :
    heightFiberMassSquare γ c = heightFiberMass γ c ^ 2 ↔ fiberVariance γ c = 0 := by
  rw [heightFiberMassSquare_eq_sq_iff_im_eq_zero hc, ← fiberVariance_eq_zero_iff hc]

/-! ## §3 The fiber mirror symmetry with multiplicity -/

/-- **Mass preservation under the Schwarz mirror.**  The packet mass is invariant under
conjugation of the centered coordinate, by the Schwarz reality `XiC_conj` and order
equivariance of the reflection. -/
theorem xiPacketMass_conj (w : ℂ) :
    xiPacketMass ((starRingEnd ℂ) w) = xiPacketMass w := by
  unfold xiPacketMass
  rw [analyticOrderAt_conj_of_conjEquivariant XiC_conj
    (XiC_analytic w (Set.mem_univ w)) (XiC_analytic _ (Set.mem_univ _))]

/-- **The fiber mirror symmetry with mass** (`d ↦ −d` with multiplicity preservation): the
Schwarz mirror of a fiber point is a fiber point of the same mass.  Off-line fiber points
therefore come in equal-mass pairs. -/
theorem heightFiber_conj_mem_mass {γ c : ℝ} (hc : 0 ≤ c) {w : ℂ}
    (hw : w ∈ heightFiber γ c) :
    (starRingEnd ℂ) w ∈ heightFiber γ c ∧
      xiPacketMass ((starRingEnd ℂ) w) = xiPacketMass w :=
  ⟨heightFiber_conj_mem hc hw, xiPacketMass_conj w⟩

/-! ## §4 The consumers: RH from the per-height mass-square identity -/

/-- Every centered Xi zero belongs to its own full-band height fiber: the strip confinement
`xiC_zero_im_mem_openHalf` places it inside the band `|Im z| ≤ 1/2`. -/
theorem mem_heightFiber_self {z : ℂ} (hz : XiC z = 0) :
    z ∈ heightFiber z.re (1 / 2) := by
  obtain ⟨h1, h2⟩ := xiC_zero_im_mem_openHalf hz
  exact (mem_heightFiber (by norm_num)).mpr ⟨rfl, ⟨by linarith, by linarith⟩, hz⟩

/-- **RH in the centered coordinate**: mathlib's `RiemannHypothesis` holds iff every zero of
the centered completed zeta function is real.  Forward is the corpus coordinate bridge;
backward pulls a putative right-half `ξ`-zero to a nonreal `XiC` zero. -/
theorem riemannHypothesis_iff_xiC_zero_im_eq_zero :
    RiemannHypothesis ↔ ∀ z : ℂ, XiC z = 0 → z.im = 0 := by
  constructor
  · intro hRH z hz
    exact xiC_zero_im_eq_zero_of_riemannHypothesis hRH hz
  · intro hreal
    rw [rh_iff_xi_ne_zero_right]
    intro ρ hρ hzero
    let z : ℂ := (ρ - 1 / 2) * (-I)
    have hXiC : XiC z = 0 := by
      rw [XiC]
      have harg : (1 : ℂ) / 2 + z * I = ρ := by
        dsimp only [z]
        rw [mul_assoc]
        have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
        rw [hI, mul_one]
        ring
      rw [harg, hzero]
    have him : z.im = 0 := hreal z hXiC
    have hzIm : z.im = 1 / 2 - ρ.re := by simp [z]
    have hre : ρ.re = 1 / 2 := by linarith
    exact (ne_of_gt (mem_rightHalf.mp hρ)) hre

/-- **RH ⟺ every height fiber lies on the critical line.**  The per-height fiber reading of
RH: the universal quantifier over heights sweeps out all centered Xi zeros. -/
theorem riemannHypothesis_iff_forall_heightFiber_im_eq_zero :
    RiemannHypothesis ↔ ∀ γ : ℝ, ∀ w ∈ heightFiber γ (1 / 2), w.im = 0 := by
  rw [riemannHypothesis_iff_xiC_zero_im_eq_zero]
  constructor
  · intro hreal γ w hw
    exact hreal w ((mem_heightFiber (by norm_num)).mp hw).2.2
  · intro hfib z hz
    exact hfib z.re z (mem_heightFiber_self hz)

/-- **RH ⟺ every height fiber is a single point.**  The census form: no height carries a
split fiber. -/
theorem riemannHypothesis_iff_forall_heightFiber_subsingleton :
    RiemannHypothesis ↔
      ∀ γ : ℝ, ∀ w ∈ heightFiber γ (1 / 2), ∀ w' ∈ heightFiber γ (1 / 2), w = w' := by
  rw [riemannHypothesis_iff_forall_heightFiber_im_eq_zero]
  exact forall_congr' fun γ => heightFiber_im_eq_zero_iff_subsingleton (by norm_num)

/-- **RH ⟺ every fiber variance vanishes** — the scalar form consumed by the module-7/8
displacement certificate. -/
theorem riemannHypothesis_iff_forall_fiberVariance_eq_zero :
    RiemannHypothesis ↔ ∀ γ : ℝ, fiberVariance γ (1 / 2) = 0 := by
  rw [riemannHypothesis_iff_forall_heightFiber_im_eq_zero]
  exact forall_congr' fun γ => (fiberVariance_eq_zero_iff (by norm_num)).symm

/-- **The maximization-certificate consumer (capstone).**  RH holds iff at every height the
fiber mass-square identity `Q = M²` holds: the `h⁻¹`-coefficient of the vertical-edge
energy saturates its unconditional ceiling `M²` exactly when the fiber mass refuses to
split off the line.  Hypothesis-free on both sides. -/
theorem riemannHypothesis_iff_forall_heightFiber_massSquare :
    RiemannHypothesis ↔
      ∀ γ : ℝ, heightFiberMassSquare γ (1 / 2) = heightFiberMass γ (1 / 2) ^ 2 := by
  rw [riemannHypothesis_iff_forall_heightFiber_im_eq_zero]
  exact forall_congr' fun γ =>
    (heightFiberMassSquare_eq_sq_iff_im_eq_zero (by norm_num)).symm

/-- **The one-sided maximization form.**  Since `Q ≤ M²` is unconditional, RH is equivalent
to the reverse inequality `M² ≤ Q` at every height: a pure lower-bound certificate. -/
theorem riemannHypothesis_iff_forall_sq_le_heightFiberMassSquare :
    RiemannHypothesis ↔
      ∀ γ : ℝ, heightFiberMass γ (1 / 2) ^ 2 ≤ heightFiberMassSquare γ (1 / 2) := by
  rw [riemannHypothesis_iff_forall_heightFiber_massSquare]
  refine forall_congr' fun γ => ⟨fun h => le_of_eq h.symm, fun h => ?_⟩
  exact le_antisymm (heightFiberMassSquare_le_sq _ _) h

end

end SlabMassSquareCertificate
end RHTower
