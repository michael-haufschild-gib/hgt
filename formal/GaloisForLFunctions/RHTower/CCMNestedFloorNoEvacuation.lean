import GaloisForLFunctions.RHTower.SuzukiParityHankelDecomposition
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Nested Rayleigh floors cannot evacuate a negative component

Let `Q` be a quadratic energy and `N` a mass on a space of trial vectors, and let `D a` be a family
of trial domains increasing in the aperture `a`.  The Rayleigh floor

```text
floor a = inf { Q v / N v : v ∈ D a, N v ≠ 0 }
```

is then **antitone** in `a`, because a larger aperture admits every smaller-aperture trial vector.
Consequently a single vector witnessing `floor a₀ ≤ -δ` witnesses the same bound at every larger
aperture, the negative part `max 0 (-floor a)` is monotone, and a cofinal limit `floor (a j) → 0`
along `a j → ∞` forces `floor a ≥ 0` for **every** `a`: a genuine negative spectral component can
never shrink away as the aperture grows.

The repair threshold

```text
η a = inf { η ≥ 0 : ∀ v ∈ D a, N v ≠ 0 → 0 ≤ Q v + η * N v }
```

is proved to be exactly `max 0 (-floor a)`, so the same conclusion holds for it.

The abstract statements are instantiated on the aperture-restricted trial domain
`apertureDomain a = {v : ℝ → ℝ | support v ⊆ (-a, a)}` with the two-variable kernel form
`diffBilinForm K v v` as energy and `∫ v²` as mass.  Zero extension is literal set inclusion there,
so the monotonicity hypothesis is discharged, and a bump function shows the quotient set is
nonempty at every positive aperture.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology Set MeasureTheory

variable {V : Type*}

/-! ## The Rayleigh floor of a domain -/

/-- The set of Rayleigh quotients of the energy/mass pair `(Q, N)` over the trial domain `D`. -/
def rayleighQuotientSet (Q N : V → ℝ) (D : Set V) : Set ℝ :=
  {r : ℝ | ∃ v ∈ D, N v ≠ 0 ∧ r = Q v / N v}

/-- The Rayleigh floor of `(Q, N)` over `D`. -/
def rayleighFloor (Q N : V → ℝ) (D : Set V) : ℝ := sInf (rayleighQuotientSet Q N D)

/-- The negative magnitude of the floor. -/
def rayleighFloorNegPart (Q N : V → ℝ) (D : Set V) : ℝ := max 0 (-rayleighFloor Q N D)

theorem mem_rayleighQuotientSet (Q N : V → ℝ) {D : Set V} {v : V} (hv : v ∈ D) (hN : N v ≠ 0) :
    Q v / N v ∈ rayleighQuotientSet Q N D := ⟨v, hv, hN, rfl⟩

theorem rayleighQuotientSet_mono (Q N : V → ℝ) {D E : Set V} (h : D ⊆ E) :
    rayleighQuotientSet Q N D ⊆ rayleighQuotientSet Q N E := by
  rintro r ⟨v, hv, hN, rfl⟩
  exact ⟨v, h hv, hN, rfl⟩

/-- **Nested-domain floor monotonicity.**  A larger trial domain has a smaller floor. -/
theorem rayleighFloor_antitone (Q N : V → ℝ) {D E : Set V} (h : D ⊆ E)
    (hbdd : BddBelow (rayleighQuotientSet Q N E))
    (hne : (rayleighQuotientSet Q N D).Nonempty) :
    rayleighFloor Q N E ≤ rayleighFloor Q N D :=
  csInf_le_csInf hbdd hne (rayleighQuotientSet_mono Q N h)

/-- **A single trial vector bounds the floor.** -/
theorem rayleighFloor_le_of_witness (Q N : V → ℝ) {E : Set V} {v : V} {c : ℝ}
    (hbdd : BddBelow (rayleighQuotientSet Q N E)) (hv : v ∈ E) (hN : N v ≠ 0)
    (hc : Q v / N v ≤ c) : rayleighFloor Q N E ≤ c :=
  le_trans (csInf_le hbdd (mem_rayleighQuotientSet Q N hv hN)) hc

/-- **The negative part is monotone in the domain.** -/
theorem rayleighFloorNegPart_mono (Q N : V → ℝ) {D E : Set V} (h : D ⊆ E)
    (hbdd : BddBelow (rayleighQuotientSet Q N E))
    (hne : (rayleighQuotientSet Q N D).Nonempty) :
    rayleighFloorNegPart Q N D ≤ rayleighFloorNegPart Q N E := by
  have hle := rayleighFloor_antitone Q N h hbdd hne
  simp only [rayleighFloorNegPart]
  exact max_le_max le_rfl (by linarith)

/-- Nonnegativity of the floor is nonnegativity of the energy on the domain. -/
theorem zero_le_rayleighFloor_iff (Q N : V → ℝ) {D : Set V}
    (hbdd : BddBelow (rayleighQuotientSet Q N D)) (hN : ∀ v ∈ D, N v ≠ 0 → 0 < N v) :
    0 ≤ rayleighFloor Q N D ↔ ∀ v ∈ D, N v ≠ 0 → 0 ≤ Q v := by
  constructor
  · intro h v hv hNv
    have hq : rayleighFloor Q N D ≤ Q v / N v := csInf_le hbdd (mem_rayleighQuotientSet Q N hv hNv)
    have hquot : 0 ≤ Q v / N v := le_trans h hq
    have hpos := hN v hv hNv
    have hmul : 0 ≤ Q v / N v * N v := mul_nonneg hquot hpos.le
    have he : Q v / N v * N v = Q v := by field_simp
    rw [he] at hmul
    exact hmul
  · intro h
    rcases (rayleighQuotientSet Q N D).eq_empty_or_nonempty with hemp | hne
    · rw [rayleighFloor, hemp, Real.sInf_empty]
    · refine le_csInf hne ?_
      rintro r ⟨v, hv, hNv, rfl⟩
      exact div_nonneg (h v hv hNv) (hN v hv hNv).le

/-! ## No cofinal evacuation -/

/-- **The evacuation theorem.**  If the floor over an increasing family of trial domains tends to
zero along some apertures tending to infinity, then it is nonnegative at every aperture.  A negative
component, once present, persists with at least its original magnitude. -/
theorem zero_le_rayleighFloor_of_tendsto_zero {Q N : V → ℝ} {D : ℝ → Set V} (a : ℝ)
    (hmono : ∀ {b c : ℝ}, b ≤ c → D b ⊆ D c)
    (hbdd : ∀ b : ℝ, BddBelow (rayleighQuotientSet Q N (D b)))
    (hne : (rayleighQuotientSet Q N (D a)).Nonempty)
    {ι : Type*} {l : Filter ι} [l.NeBot] {aseq : ι → ℝ}
    (hseq : Tendsto aseq l atTop)
    (hlim : Tendsto (fun i => rayleighFloor Q N (D (aseq i))) l (nhds 0)) :
    0 ≤ rayleighFloor Q N (D a) := by
  by_contra hneg
  rw [not_le] at hneg
  set δ : ℝ := -rayleighFloor Q N (D a) with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have h1 : ∀ᶠ i in l, a ≤ aseq i := hseq.eventually_ge_atTop a
  have h2 : ∀ᶠ i in l, rayleighFloor Q N (D (aseq i)) ≤ -δ := by
    filter_upwards [h1] with i hi
    have := rayleighFloor_antitone Q N (hmono hi) (hbdd (aseq i)) hne
    rw [hδ]
    linarith
  have h3 : ∀ᶠ i in l, -δ / 2 < rayleighFloor Q N (D (aseq i)) :=
    hlim.eventually (eventually_gt_nhds (show -δ / 2 < (0 : ℝ) by linarith))
  obtain ⟨i, hi2, hi3⟩ := (h2.and h3).exists
  linarith

/-! ## The repair threshold -/

/-- The admissible scalar repairs: shifts of the mass making the energy nonnegative. -/
def repairSet (Q N : V → ℝ) (D : Set V) : Set ℝ :=
  {η : ℝ | 0 ≤ η ∧ ∀ v ∈ D, N v ≠ 0 → 0 ≤ Q v + η * N v}

/-- The repair threshold: the least admissible scalar shift. -/
def repairThreshold (Q N : V → ℝ) (D : Set V) : ℝ := sInf (repairSet Q N D)

theorem repairSet_eq_Ici (Q N : V → ℝ) {D : Set V}
    (hN : ∀ v ∈ D, N v ≠ 0 → 0 < N v) (hbdd : BddBelow (rayleighQuotientSet Q N D)) :
    repairSet Q N D = Ici (rayleighFloorNegPart Q N D) := by
  ext η
  simp only [repairSet, rayleighFloorNegPart, mem_setOf_eq, mem_Ici, max_le_iff]
  constructor
  · rintro ⟨hη0, hall⟩
    refine ⟨hη0, ?_⟩
    have hfloor : -η ≤ rayleighFloor Q N D := by
      rcases (rayleighQuotientSet Q N D).eq_empty_or_nonempty with hemp | hne
      · rw [rayleighFloor, hemp, Real.sInf_empty]; linarith
      · refine le_csInf hne ?_
        rintro r ⟨v, hv, hNv, rfl⟩
        have hpos := hN v hv hNv
        have hshift := hall v hv hNv
        rw [le_div_iff₀ hpos]
        linarith
    linarith
  · rintro ⟨hη0, hle⟩
    refine ⟨hη0, ?_⟩
    intro v hv hNv
    have hpos := hN v hv hNv
    have hq : rayleighFloor Q N D ≤ Q v / N v := csInf_le hbdd (mem_rayleighQuotientSet Q N hv hNv)
    have hstep : -η ≤ Q v / N v := by linarith
    rw [le_div_iff₀ hpos] at hstep
    linarith

/-- **The repair threshold is exactly the negative part of the floor.** -/
theorem repairThreshold_eq_negPart (Q N : V → ℝ) {D : Set V}
    (hN : ∀ v ∈ D, N v ≠ 0 → 0 < N v) (hbdd : BddBelow (rayleighQuotientSet Q N D)) :
    repairThreshold Q N D = rayleighFloorNegPart Q N D := by
  rw [repairThreshold, repairSet_eq_Ici Q N hN hbdd, csInf_Ici]

/-- **The repair threshold is monotone in the domain.** -/
theorem repairThreshold_mono (Q N : V → ℝ) {D E : Set V} (h : D ⊆ E)
    (hND : ∀ v ∈ D, N v ≠ 0 → 0 < N v) (hNE : ∀ v ∈ E, N v ≠ 0 → 0 < N v)
    (hbddD : BddBelow (rayleighQuotientSet Q N D))
    (hbddE : BddBelow (rayleighQuotientSet Q N E))
    (hne : (rayleighQuotientSet Q N D).Nonempty) :
    repairThreshold Q N D ≤ repairThreshold Q N E := by
  rw [repairThreshold_eq_negPart Q N hND hbddD, repairThreshold_eq_negPart Q N hNE hbddE]
  exact rayleighFloorNegPart_mono Q N h hbddE hne

/-- **A cofinal vanishing repair threshold vanishes everywhere.** -/
theorem repairThreshold_eq_zero_of_tendsto_zero {Q N : V → ℝ} {D : ℝ → Set V} (a : ℝ)
    (hmono : ∀ {b c : ℝ}, b ≤ c → D b ⊆ D c)
    (hN : ∀ b : ℝ, ∀ v ∈ D b, N v ≠ 0 → 0 < N v)
    (hbdd : ∀ b : ℝ, BddBelow (rayleighQuotientSet Q N (D b)))
    (hne : (rayleighQuotientSet Q N (D a)).Nonempty)
    {ι : Type*} {l : Filter ι} [l.NeBot] {aseq : ι → ℝ}
    (hseq : Tendsto aseq l atTop)
    (hlim : Tendsto (fun i => rayleighFloor Q N (D (aseq i))) l (nhds 0)) :
    repairThreshold Q N (D a) = 0 := by
  have hfloor := zero_le_rayleighFloor_of_tendsto_zero a hmono hbdd hne hseq hlim
  rw [repairThreshold_eq_negPart Q N (hN a) (hbdd a), rayleighFloorNegPart]
  exact max_eq_left (by linarith)

/-! ## The aperture-restricted instantiation -/

/-- The aperture-restricted trial domain: functions vanishing off `(-a, a)`. -/
def apertureDomain (a : ℝ) : Set (ℝ → ℝ) := {v | ∀ x, v x ≠ 0 → x ∈ Ioo (-a) a}

/-- Zero extension is literal inclusion of aperture domains. -/
theorem apertureDomain_mono {a b : ℝ} (h : a ≤ b) : apertureDomain a ⊆ apertureDomain b := by
  intro v hv x hx
  obtain ⟨h1, h2⟩ := hv x hx
  exact ⟨by linarith, by linarith⟩

/-- The `L²` mass of a trial function. -/
def sqMass (v : ℝ → ℝ) : ℝ := ∫ x : ℝ, v x ^ (2 : ℕ)

/-- The restricted floor of the two-variable kernel form at aperture `a`. -/
def restrictedKernelFloor (K : ℝ → ℝ) (a : ℝ) : ℝ :=
  rayleighFloor (fun v => diffBilinForm K v v) sqMass (apertureDomain a)

/-- **The restricted kernel floor is antitone in the aperture.** -/
theorem restrictedKernelFloor_antitone (K : ℝ → ℝ) {a b : ℝ} (h : a ≤ b)
    (hbdd : BddBelow
      (rayleighQuotientSet (fun v => diffBilinForm K v v) sqMass (apertureDomain b)))
    (hne : (rayleighQuotientSet (fun v => diffBilinForm K v v) sqMass
      (apertureDomain a)).Nonempty) :
    restrictedKernelFloor K b ≤ restrictedKernelFloor K a :=
  rayleighFloor_antitone _ _ (apertureDomain_mono h) hbdd hne

/-- **The trial set is nonempty at every positive aperture.**  A smooth bump supported in `(-a, a)`
has positive mass, so the floor is not a junk value. -/
theorem rayleighQuotientSet_apertureDomain_nonempty (K : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    (rayleighQuotientSet (fun v => diffBilinForm K v v) sqMass (apertureDomain a)).Nonempty := by
  classical
  set F : ContDiffBump (0 : ℝ) := ⟨a / 2, a, by linarith, by linarith⟩ with hF
  have hFout : F.rOut = a := rfl
  have hsupp : Function.support (F : ℝ → ℝ) = Ioo (-a) a := by
    rw [F.support_eq, hFout, Real.ball_eq_Ioo]
    norm_num
  have hmem : (F : ℝ → ℝ) ∈ apertureDomain a := by
    intro x hx
    rw [← hsupp]
    exact hx
  have hsup2 : (Function.support fun x : ℝ => (F : ℝ → ℝ) x ^ (2 : ℕ)) = Ioo (-a) a := by
    rw [← hsupp]
    ext x
    simp [Function.mem_support]
  have hcs : HasCompactSupport fun x : ℝ => (F : ℝ → ℝ) x ^ (2 : ℕ) := by
    have h := F.hasCompactSupport
    simp only [HasCompactSupport, tsupport] at h ⊢
    rw [hsup2, ← hsupp]
    exact h
  have hint : Integrable fun x : ℝ => (F : ℝ → ℝ) x ^ (2 : ℕ) :=
    (F.continuous.pow 2).integrable_of_hasCompactSupport hcs
  have hnn : (0 : ℝ → ℝ) ≤ fun x : ℝ => (F : ℝ → ℝ) x ^ (2 : ℕ) := fun x => sq_nonneg _
  have hpos : 0 < ∫ x : ℝ, (F : ℝ → ℝ) x ^ (2 : ℕ) := by
    rw [integral_pos_iff_support_of_nonneg hnn hint, hsup2, Real.volume_Ioo]
    have : (0 : ℝ) < a - -a := by linarith
    simpa using this
  exact ⟨_, mem_rayleighQuotientSet _ _ hmem (ne_of_gt hpos)⟩

end GaloisForLFunctions.RHTower

end
