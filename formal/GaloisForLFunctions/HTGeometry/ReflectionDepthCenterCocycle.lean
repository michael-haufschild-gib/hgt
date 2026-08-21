import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

/-!
# Reflection--depth center cocycle and half-density compensation

A strict one-dimensional affine multiplicative formation law is a dilation about one common
centre, so its translation cocycle is a coboundary.  Exchanging such a dilation with a marked
reflection produces a translation measuring the mismatch of the two centres, and the unique affine
slope-`λ` map commuting with the reflection is the centred dilation.  A nonzero mismatch escapes
every bounded admission chamber and every proper source work, while its projection to a circle is
recurrent: a closed observer does not close the formation history.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory

noncomputable section

/-! ## The common-centre classification -/

/-- **Common-centre classification** (card `(RFC.4)`).  A strict affine multiplicative formation
law has one common centre, and its translation cocycle is the corresponding coboundary. -/
theorem exists_unique_formationCenter {M : Set ℝ} {b : ℝ → ℝ}
    (hcocycle : ∀ l ∈ M, ∀ m ∈ M, b (l * m) = l * b m + b l)
    {ρ : ℝ} (hρ : ρ ∈ M) (hρ1 : ρ ≠ 1) :
    ∃! d : ℝ, ∀ l ∈ M, b l = (1 - l) * d := by
  have hne : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ1)
  refine ⟨b ρ / (1 - ρ), fun l hl => ?_, fun d hd => ?_⟩
  · have h1 := hcocycle l hl ρ hρ
    have h2 := hcocycle ρ hρ l hl
    rw [mul_comm ρ l] at h2
    have hkey : (l - 1) * b ρ = (ρ - 1) * b l := by linarith
    field_simp
    linarith [hkey]
  · have := hd ρ hρ
    field_simp
    linarith [this]

/-- The centred dilation of slope `l` about `d`. -/
def dilate (d l x : ℝ) : ℝ := d + l * (x - d)

/-- The reflection about `c`. -/
def reflect (c x : ℝ) : ℝ := 2 * c - x

@[simp] theorem dilate_one (d x : ℝ) : dilate d 1 x = x := by
  rw [dilate]; ring

theorem dilate_dilate (d l m x : ℝ) : dilate d l (dilate d m x) = dilate d (l * m) x := by
  rw [dilate, dilate, dilate]; ring

theorem dilate_affine (d l x : ℝ) : dilate d l x = l * x + (1 - l) * d := by
  rw [dilate]; ring

@[simp] theorem reflect_reflect (c x : ℝ) : reflect c (reflect c x) = x := by
  rw [reflect, reflect]; ring

/-! ## The reflection exchange defect -/

/-- **Exact schedule exchange** (card `(RFC.7)`). -/
theorem dilate_reflect (d c l x : ℝ) :
    dilate d l (reflect c x) = reflect c (dilate d l x) + 2 * (l - 1) * (c - d) := by
  rw [dilate, dilate, reflect, reflect]; ring

/-- **The exchange word is a translation** (card `(RFC.8)`). -/
theorem exchange_word (d c l x : ℝ) (hl : l ≠ 0) :
    dilate d l (reflect c (dilate d l⁻¹ (reflect c x))) = x + 2 * (l - 1) * (c - d) := by
  rw [dilate, dilate, reflect, reflect]
  field_simp
  ring

/-- **Commutation holds exactly at equal centres.** -/
theorem dilate_reflect_comm_iff {l : ℝ} (hl : l ≠ 1) (d c : ℝ) :
    (∀ x, dilate d l (reflect c x) = reflect c (dilate d l x)) ↔ d = c := by
  constructor
  · intro h
    have h0 := h 0
    rw [dilate_reflect] at h0
    have hne : l - 1 ≠ 0 := sub_ne_zero.2 hl
    have : 2 * (l - 1) * (c - d) = 0 := by linarith
    rcases mul_eq_zero.1 this with hz | hz
    · rcases mul_eq_zero.1 hz with hz2 | hz2
      · norm_num at hz2
      · exact absurd hz2 hne
    · linarith
  · rintro rfl
    intro x
    rw [dilate_reflect]
    ring

/-- **Iterated exchange** (card `(RFC.9)`). -/
theorem exchange_iterate (h x : ℝ) (n : ℕ) : (fun y => y + h)^[n] x = x + n * h := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      push_cast
      ring

/-! ## The unique reflection-compatible compensation -/

/-- **Unique centred dilation** (card `(RFC.10)`).  Among affine maps of a given slope, exactly one
commutes with the reflection. -/
theorem affine_comm_reflect_iff (c l b : ℝ) :
    (∀ x, l * reflect c x + b = reflect c (l * x + b)) ↔ b = (1 - l) * c := by
  constructor
  · intro h
    have h0 := h 0
    rw [reflect, reflect] at h0
    linarith
  · rintro rfl
    intro x
    rw [reflect, reflect]
    ring

/-- The centred dilation family is a strict multiplicative action commuting with the reflection
(card `(RFC.11)`). -/
theorem dilate_center_comm (c l x : ℝ) : dilate c l (reflect c x) = reflect c (dilate c l x) := by
  rw [dilate_reflect]; ring

/-! ## The functional-equation specialization -/

/-- The Dirichlet functional reflection. -/
def dirichletReflect (σ : ℝ) : ℝ := 1 - σ

theorem dirichletReflect_eq (σ : ℝ) : dirichletReflect σ = reflect (1 / 2) σ := by
  rw [dirichletReflect, reflect]; ring

/-- **Raw depth and functional reflection do not commute** (card `(RFC.13)`). -/
theorem rawDepth_reflect (m σ : ℝ) :
    m * dirichletReflect σ = dirichletReflect (m * σ) + (m - 1) := by
  rw [dirichletReflect, dirichletReflect]; ring

theorem rawDepth_exchange_word (m σ : ℝ) (hm : m ≠ 0) :
    m * dirichletReflect (m⁻¹ * dirichletReflect σ) = σ + (m - 1) := by
  rw [dirichletReflect, dirichletReflect]
  field_simp
  ring

/-- The unique reflection-compatible depth action (card `(RFC.14)`). -/
def compensatedDepth (m σ : ℝ) : ℝ := m * σ - (m - 1) / 2

theorem compensatedDepth_eq_dilate (m σ : ℝ) :
    compensatedDepth m σ = dilate (1 / 2) m σ := by
  rw [compensatedDepth, dilate]; ring

theorem compensatedDepth_reflect (m σ : ℝ) :
    compensatedDepth m (dirichletReflect σ) = dirichletReflect (compensatedDepth m σ) := by
  rw [compensatedDepth, compensatedDepth, dirichletReflect, dirichletReflect]; ring

/-- **The half-density coefficient law** (card `(RFC.15)`). -/
theorem dirichletWeight_compensatedDepth {n : ℝ} (hn : 0 < n) (m σ : ℝ) :
    n ^ (-compensatedDepth m σ) = n ^ ((m - 1) / 2) * (n ^ (-σ)) ^ m := by
  rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn, compensatedDepth]
  congr 1
  ring

/-! ## Bounded admission and proper work -/

/-- **Bounded-admission escape** (card `(RFC.16)`). -/
theorem step_le_of_forall_mem {A : Set ℝ} {L : ℝ}
    (hA : ∀ y ∈ A, ∀ z ∈ A, |y - z| ≤ L) (x h : ℝ) (N : ℕ)
    (hmem : ∀ k : ℕ, k ≤ N → x + k * h ∈ A) : (N : ℝ) * |h| ≤ L := by
  have h0 := hmem 0 (Nat.zero_le N)
  have hN := hmem N le_rfl
  have := hA _ h0 _ hN
  simp only [Nat.cast_zero, zero_mul, add_zero] at this
  rw [show x - (x + (N : ℝ) * h) = -((N : ℝ) * h) from by ring, abs_neg, abs_mul,
    Nat.abs_cast] at this
  exact this

/-- **Proper-work escape** (card `(RFC.17)`). -/
theorem tendsto_properWork_atTop {C : ℝ → ℝ} (hC : ∀ r : ℝ, IsCompact {y : ℝ | C y ≤ r})
    {x h : ℝ} (hh : h ≠ 0) :
    Filter.Tendsto (fun n : ℕ => C (x + n * h)) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun r => ?_
  obtain ⟨R, hR⟩ := (hC r).isBounded.subset_closedBall 0
  have hhpos : 0 < |h| := abs_pos.2 hh
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + |x|) / |h|)
  refine Filter.eventually_atTop.2 ⟨N, fun n hn => ?_⟩
  by_contra hlt
  have hmem : x + (n : ℝ) * h ∈ {y : ℝ | C y ≤ r} := le_of_not_ge hlt
  have hball := hR hmem
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hball
  have hbig : (R + |x|) / |h| < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
  rw [div_lt_iff₀ hhpos] at hbig
  have habs : (n : ℝ) * |h| - |x| ≤ |x + (n : ℝ) * h| := by
    have := abs_sub_abs_le_abs_sub ((n : ℝ) * h) (-x)
    rw [sub_neg_eq_add, abs_neg] at this
    calc (n : ℝ) * |h| - |x| = |(n : ℝ) * h| - |x| := by
          rw [abs_mul, Nat.abs_cast]
      _ ≤ |(n : ℝ) * h + x| := this
      _ = |x + (n : ℝ) * h| := by rw [add_comm]
  linarith

/-! ## Common recovery conserves the exchange defect -/

/-- **Common recovery is information-neutral, not defect-neutral** (card `(RFC.20)`).  Along the
exchange translation orbit the formed-packet Jeffreys work equals the base Jeffreys work exactly. -/
theorem formationJeffreys_translationOrbit {Ω K : Type*} [MeasurableSpace Ω] [MeasurableSpace K]
    (μ : ℝ → Measure Ω) (hfin : ∀ t : ℝ, IsFiniteMeasure (μ t)) (κ : Kernel Ω K)
    [IsMarkovKernel κ] (x h : ℝ) (n : ℕ) :
    formationJeffreys (splitFormation (μ x) κ) (splitFormation (μ (x + n * h)) κ)
      = formationJeffreys (μ x) (μ (x + n * h)) := by
  haveI := hfin x
  haveI := hfin (x + n * h)
  exact formationJeffreys_splitFormation _ _ κ

/-! ## Recurrent observer, open history -/

/-- **The lifted exchange history is unbounded** (card `(RFC.22)`, lift side). -/
theorem not_isBounded_translation_orbit {x h : ℝ} (hh : h ≠ 0) :
    ¬ Bornology.IsBounded (Set.range fun n : ℕ => x + n * h) := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hhpos : 0 < |h| := abs_pos.2 hh
  obtain ⟨N, hN⟩ := exists_nat_gt ((R + |x|) / |h|)
  have hmem : x + (N : ℝ) * h ∈ Set.range fun n : ℕ => x + n * h := ⟨N, rfl⟩
  have hball := hR hmem
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hball
  rw [div_lt_iff₀ hhpos] at hN
  have habs : (N : ℝ) * |h| - |x| ≤ |x + (N : ℝ) * h| := by
    have := abs_sub_abs_le_abs_sub ((N : ℝ) * h) (-x)
    rw [sub_neg_eq_add, abs_neg] at this
    calc (N : ℝ) * |h| - |x| = |(N : ℝ) * h| - |x| := by
          rw [abs_mul, Nat.abs_cast]
      _ ≤ |(N : ℝ) * h + x| := this
      _ = |x + (N : ℝ) * h| := by rw [add_comm]
  linarith

/-- **The projected exchange observer is recurrent** (card `(RFC.22)`, observer side): its closure
is compact. -/
theorem isCompact_closure_projected_orbit (ℓ : ℝ) [Fact (0 < ℓ)] (x h : ℝ) :
    IsCompact (closure (Set.range fun n : ℕ => ((x + n * h : ℝ) : AddCircle ℓ))) :=
  isClosed_closure.isCompact

/-- **Rational increment: the projected orbit is periodic.** -/
theorem projected_orbit_periodic (ℓ : ℝ) (x h : ℝ) {p : ℤ} {q : ℕ}
    (hpq : (q : ℝ) * h = p * ℓ) (n : ℕ) :
    ((x + (n + q : ℕ) * h : ℝ) : AddCircle ℓ) = ((x + n * h : ℝ) : AddCircle ℓ) := by
  have hsplit : x + ((n + q : ℕ) : ℝ) * h = (x + (n : ℝ) * h) + (p : ℝ) * ℓ := by
    push_cast
    linarith [hpq]
  have hzero : (((p : ℝ) * ℓ : ℝ) : AddCircle ℓ) = 0 := by
    have h1 : ((p : ℝ) * ℓ) = (p : ℤ) • ℓ := by ring
    rw [h1, show ((((p : ℤ) • ℓ : ℝ)) : AddCircle ℓ) = (p : ℤ) • ((ℓ : ℝ) : AddCircle ℓ) from rfl,
      AddCircle.coe_period, smul_zero]
  rw [hsplit,
    show (((x + (n : ℝ) * h) + (p : ℝ) * ℓ : ℝ) : AddCircle ℓ)
      = ((x + (n : ℝ) * h : ℝ) : AddCircle ℓ) + (((p : ℝ) * ℓ : ℝ) : AddCircle ℓ) from rfl,
    hzero, add_zero]

/-- **Irrational increment: the exchange rotation is dense** (card `§7`). -/
theorem denseRange_projected_increment {ℓ h : ℝ} (hirr : Irrational (h / ℓ)) :
    DenseRange fun k : ℤ => (k • (h : AddCircle ℓ)) :=
  AddCircle.denseRange_zsmul_coe_iff.2 hirr

end

end GaloisForLFunctions.HTGeometry
