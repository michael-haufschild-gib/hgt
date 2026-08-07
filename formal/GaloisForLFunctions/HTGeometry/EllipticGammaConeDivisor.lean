import GaloisForLFunctions.HTGeometry.ExpConeProduct
import GaloisForLFunctions.HTGeometry.TripticSourceDivisor
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# The elliptic gamma function and its quadrant divisor

The elliptic gamma function is the ratio of two exponential cone products,

`Γ(z; a, b) = Φ(a + b - z) / Φ(z)`,   `Φ(z) = ∏_{j,k ≥ 0} (1 - e(j a + k b + z))`.

When `1, a, b` are independent over `ℤ`, every zero of `Φ` comes from exactly one factor, so all
zeros are simple, and the zero and pole sets of `Γ` are the two disjoint quadrants

zeros: `z = (j+1) a + (k+1) b - m`,   poles: `z = m - j a - k b`   (`j, k ≥ 0`, `m ∈ ℤ`).

Along the `b`-orbit of the origin the pole order is `-1` for `m ≤ 0` and `0` for `m > 0`: a half
line, not a finite set.  Its shift differences are therefore supported at the single index `m = 0`,
and the orbital charge is `1`.  This is the realization statement behind surjectivity of the triptic
divisor map: a theta function, whose divisor meets each orbit finitely, would give charge `0`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- `ℤ`-independence of `1, a, b`. -/
def IndepPeriods (a b : ℂ) : Prop :=
  ∀ p q r : ℤ, (p : ℂ) + q * a + r * b = 0 → p = 0 ∧ q = 0 ∧ r = 0

/-! ### The zero set of the cone product -/

theorem coneProduct_eq_zero_iff' {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) (z : ℂ) :
    coneProduct a b z = 0 ↔ ∃ (j k : ℕ) (m : ℤ), (j : ℂ) * a + (k : ℂ) * b + z = (m : ℂ) := by
  rw [coneProduct_eq_zero_iff ha hb]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨m, hm⟩ := (coneFactor_eq_zero_iff a b n z).mp hn
    exact ⟨n.1, n.2, m, hm⟩
  · rintro ⟨j, k, m, hm⟩
    exact ⟨(j, k), (coneFactor_eq_zero_iff a b (j, k) z).mpr ⟨m, hm⟩⟩

/-- Under independence a point of the zero set is hit by exactly one factor. -/
theorem coneFactor_index_unique {a b : ℂ} (hindep : IndepPeriods a b) {z : ℂ} {n n' : ℕ × ℕ}
    (h : coneFactor a b n z = 0) (h' : coneFactor a b n' z = 0) : n = n' := by
  rw [coneFactor_eq_zero_iff] at h h'
  obtain ⟨m, hm⟩ := h
  obtain ⟨m', hm'⟩ := h'
  have hz : ((m - m' : ℤ) : ℂ) + (((n'.1 : ℤ) - (n.1 : ℤ)) : ℤ) * a
      + (((n'.2 : ℤ) - (n.2 : ℤ)) : ℤ) * b = 0 := by
    push_cast
    linear_combination hm' - hm
  obtain ⟨-, h2, h3⟩ := hindep _ _ _ hz
  have e1 : n.1 = n'.1 := by omega
  have e2 : n.2 = n'.2 := by omega
  exact Prod.ext e1 e2

/-- **Every zero of the cone product is simple.** -/
theorem analyticOrderAt_coneProduct_of_zero {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) {z : ℂ} (hz : coneProduct a b z = 0) :
    analyticOrderAt (coneProduct a b) z = 1 := by
  obtain ⟨n₀, hn₀⟩ := (coneProduct_eq_zero_iff ha hb z).mp hz
  refine analyticOrderAt_coneProduct_eq_one ha hb hn₀ fun n hn hcontra => ?_
  exact hn (coneFactor_index_unique hindep hcontra hn₀)

theorem meromorphicOrderAt_coneProduct {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (z : ℂ) :
    meromorphicOrderAt (coneProduct a b) z = if coneProduct a b z = 0 then 1 else 0 := by
  have han : AnalyticAt ℂ (coneProduct a b) z := (differentiable_coneProduct ha hb).analyticAt z
  rw [han.meromorphicOrderAt_eq]
  by_cases hz : coneProduct a b z = 0
  · rw [if_pos hz, analyticOrderAt_coneProduct_of_zero ha hb hindep hz]
    rfl
  · rw [if_neg hz, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
    rfl

/-! ### The elliptic gamma function -/

/-- The elliptic gamma function as a ratio of exponential cone products. -/
noncomputable def ellipticGammaCone (a b : ℂ) : ℂ → ℂ :=
  (fun z => coneProduct a b (a + b - z)) / coneProduct a b

theorem differentiable_ellipticGammaConeNum {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im) :
    Differentiable ℂ (fun z => coneProduct a b (a + b - z)) :=
  (differentiable_coneProduct ha hb).comp (by fun_prop)

/-! ### The orbit through the origin -/

/-- **The pole half line.**  The cone product vanishes at `m·b` exactly when `m ≤ 0`. -/
theorem coneProduct_orbit_eq_zero_iff {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (m : ℤ) :
    coneProduct a b ((m : ℂ) * b) = 0 ↔ m ≤ 0 := by
  rw [coneProduct_eq_zero_iff' ha hb]
  constructor
  · rintro ⟨j, k, m', hm'⟩
    have hz : ((-m' : ℤ) : ℂ) + ((j : ℤ) : ℤ) * a + (((k : ℤ) + m) : ℤ) * b = 0 := by
      push_cast
      linear_combination hm'
    obtain ⟨-, -, h3⟩ := hindep _ _ _ hz
    omega
  · intro hm
    refine ⟨0, (-m).toNat, 0, ?_⟩
    have hk : (((-m).toNat : ℤ) : ℂ) = ((-m : ℤ) : ℂ) := by
      norm_cast
      omega
    push_cast at hk ⊢
    rw [hk]
    ring

/-- **The numerator never vanishes on that orbit.** -/
theorem coneProduct_num_orbit_ne_zero {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (m : ℤ) :
    coneProduct a b (a + b - (m : ℂ) * b) ≠ 0 := by
  intro hzero
  obtain ⟨j, k, m', hm'⟩ := (coneProduct_eq_zero_iff' ha hb _).mp hzero
  have hz : ((-m' : ℤ) : ℂ) + (((j : ℤ) + 1) : ℤ) * a + (((k : ℤ) + 1 - m) : ℤ) * b = 0 := by
    push_cast
    linear_combination hm'
  obtain ⟨-, h2, -⟩ := hindep _ _ _ hz
  omega

/-- **The pole order along the orbit.** -/
theorem meromorphicOrderAt_ellipticGammaCone_orbit {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (m : ℤ) :
    meromorphicOrderAt (ellipticGammaCone a b) ((m : ℂ) * b) = if m ≤ 0 then -1 else 0 := by
  have hnum : MeromorphicAt (fun z => coneProduct a b (a + b - z)) ((m : ℂ) * b) :=
    ((differentiable_ellipticGammaConeNum ha hb).analyticAt _).meromorphicAt
  have hden : MeromorphicAt (coneProduct a b) ((m : ℂ) * b) :=
    ((differentiable_coneProduct ha hb).analyticAt _).meromorphicAt
  rw [ellipticGammaCone, meromorphicOrderAt_div hnum hden]
  have hnumOrder : meromorphicOrderAt (fun z => coneProduct a b (a + b - z)) ((m : ℂ) * b) = 0 := by
    have han : AnalyticAt ℂ (fun z => coneProduct a b (a + b - z)) ((m : ℂ) * b) :=
      (differentiable_ellipticGammaConeNum ha hb).analyticAt _
    have hval : (fun z => coneProduct a b (a + b - z)) ((m : ℂ) * b) ≠ 0 :=
      coneProduct_num_orbit_ne_zero ha hb hindep m
    rw [han.meromorphicOrderAt_eq,
      (analyticOrderAt_eq_zero (𝕜 := ℂ) (E := ℂ)
        (f := fun z : ℂ => coneProduct a b (a + b - z)) (z₀ := (m : ℂ) * b)).mpr (Or.inr hval)]
    rfl
  rw [hnumOrder, meromorphicOrderAt_coneProduct ha hb hindep]
  by_cases hm : m ≤ 0
  · rw [if_pos ((coneProduct_orbit_eq_zero_iff ha hb hindep m).mpr hm), if_pos hm]
    rfl
  · rw [if_neg (fun h => hm ((coneProduct_orbit_eq_zero_iff ha hb hindep m).mp h)), if_neg hm]
    rfl

/-- **The shift order is supported at the single index `0`.** -/
theorem shiftOrder_ellipticGammaCone_orbit {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (m : ℤ) :
    shiftOrder (ellipticGammaCone a b) b (0 + (m : ℂ) * b) = if m = 0 then 1 else 0 := by
  have hstep : (0 : ℂ) + (m : ℂ) * b + b = (((m + 1 : ℤ) : ℂ)) * b := by push_cast; ring
  have hbase : (0 : ℂ) + (m : ℂ) * b = ((m : ℤ) : ℂ) * b := by ring
  rw [shiftOrder, hstep, hbase, meromorphicOrderAt_ellipticGammaCone_orbit ha hb hindep,
    meromorphicOrderAt_ellipticGammaCone_orbit ha hb hindep]
  by_cases h0 : m = 0
  · subst h0
    norm_num
  · by_cases hm : m ≤ 0
    · have hm1 : m + 1 ≤ 0 := by omega
      rw [if_pos hm1, if_pos hm, if_neg h0]
      norm_num
    · have hm1 : ¬ (m + 1 ≤ 0) := by omega
      rw [if_neg hm1, if_neg hm, if_neg h0]
      norm_num

/-- **The elliptic gamma function realizes the unit orbital charge.** -/
theorem tripticOrbitCharge_ellipticGammaCone {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) :
    tripticOrbitCharge (ellipticGammaCone a b) b 0 = 1 := by
  rw [tripticOrbitCharge]
  rw [finsum_congr (shiftOrder_ellipticGammaCone_orbit ha hb hindep)]
  rw [finsum_eq_single (fun m : ℤ => if m = 0 then (1 : ℤ) else 0) 0 (fun x hx => if_neg hx)]
  norm_num

/-! ### Translation realizes every class -/

/-- The translated elliptic gamma source. -/
noncomputable def ellipticGammaConeTranslate (a b g : ℂ) : ℂ → ℂ :=
  fun z => ellipticGammaCone a b (z - g)

theorem shiftOrder_ellipticGammaConeTranslate {a b g : ℂ} (σ w : ℂ) :
    shiftOrder (ellipticGammaConeTranslate a b g) σ w
      = shiftOrder (ellipticGammaCone a b) σ (w - g) := by
  have hcomp : ellipticGammaConeTranslate a b g
      = fun z => ellipticGammaCone a b (z + (-g)) := by
    funext z
    simp [ellipticGammaConeTranslate, sub_eq_add_neg]
  rw [shiftOrder, shiftOrder, hcomp, meromorphicOrderAt_comp_add, meromorphicOrderAt_comp_add]
  congr 3
  ring

/-- **Every class is realized.**  The translate of the elliptic gamma source by `g` has orbital
charge `1` on the orbit through `g`. -/
theorem tripticOrbitCharge_ellipticGammaConeTranslate {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (g : ℂ) :
    tripticOrbitCharge (ellipticGammaConeTranslate a b g) b g = 1 := by
  rw [tripticOrbitCharge]
  have hterm : ∀ m : ℤ,
      shiftOrder (ellipticGammaConeTranslate a b g) b (g + (m : ℂ) * b)
        = shiftOrder (ellipticGammaCone a b) b (0 + (m : ℂ) * b) := by
    intro m
    rw [shiftOrder_ellipticGammaConeTranslate]
    congr 1
    ring
  rw [finsum_congr hterm, ← tripticOrbitCharge]
  exact tripticOrbitCharge_ellipticGammaCone ha hb hindep

/-! ### Charge zero off the class -/

/-- The period group generated by `1`, `a`, `b`. -/
def PeriodGroupMem (a b p : ℂ) : Prop := ∃ c q r : ℤ, p = (c : ℂ) + q * a + r * b

theorem coneProduct_orbit_ne_zero_of_notMem {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    {p : ℂ} (hp : ¬ PeriodGroupMem a b p) (m : ℤ) :
    coneProduct a b (p + (m : ℂ) * b) ≠ 0 := by
  intro hzero
  obtain ⟨j, k, m', hm'⟩ := (coneProduct_eq_zero_iff' ha hb _).mp hzero
  exact hp ⟨m', -(j : ℤ), -((k : ℤ) + m), by push_cast; linear_combination hm'⟩

theorem coneProduct_num_orbit_ne_zero_of_notMem {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    {p : ℂ} (hp : ¬ PeriodGroupMem a b p) (m : ℤ) :
    coneProduct a b (a + b - (p + (m : ℂ) * b)) ≠ 0 := by
  intro hzero
  obtain ⟨j, k, m', hm'⟩ := (coneProduct_eq_zero_iff' ha hb _).mp hzero
  exact hp ⟨-m', (j : ℤ) + 1, (k : ℤ) + 1 - m, by push_cast; linear_combination -hm'⟩

theorem meromorphicOrderAt_ellipticGammaCone_orbit_of_notMem {a b : ℂ} (ha : 0 < a.im)
    (hb : 0 < b.im) {p : ℂ} (hp : ¬ PeriodGroupMem a b p) (m : ℤ) :
    meromorphicOrderAt (ellipticGammaCone a b) (p + (m : ℂ) * b) = 0 := by
  have hnum : MeromorphicAt (fun z => coneProduct a b (a + b - z)) (p + (m : ℂ) * b) :=
    ((differentiable_ellipticGammaConeNum ha hb).analyticAt _).meromorphicAt
  have hden : MeromorphicAt (coneProduct a b) (p + (m : ℂ) * b) :=
    ((differentiable_coneProduct ha hb).analyticAt _).meromorphicAt
  rw [ellipticGammaCone, meromorphicOrderAt_div hnum hden]
  have hnumOrder : meromorphicOrderAt (fun z => coneProduct a b (a + b - z))
      (p + (m : ℂ) * b) = 0 := by
    have han : AnalyticAt ℂ (fun z => coneProduct a b (a + b - z)) (p + (m : ℂ) * b) :=
      (differentiable_ellipticGammaConeNum ha hb).analyticAt _
    have hval : (fun z => coneProduct a b (a + b - z)) (p + (m : ℂ) * b) ≠ 0 :=
      coneProduct_num_orbit_ne_zero_of_notMem ha hb hp m
    rw [han.meromorphicOrderAt_eq,
      (analyticOrderAt_eq_zero (𝕜 := ℂ) (E := ℂ)
        (f := fun z : ℂ => coneProduct a b (a + b - z)) (z₀ := p + (m : ℂ) * b)).mpr
        (Or.inr hval)]
    rfl
  have hdenOrder : meromorphicOrderAt (coneProduct a b) (p + (m : ℂ) * b) = 0 := by
    have han : AnalyticAt ℂ (coneProduct a b) (p + (m : ℂ) * b) :=
      (differentiable_coneProduct ha hb).analyticAt _
    rw [han.meromorphicOrderAt_eq,
      analyticOrderAt_eq_zero.mpr (Or.inr (coneProduct_orbit_ne_zero_of_notMem ha hb hp m))]
    rfl
  rw [hnumOrder, hdenOrder, sub_zero]

/-- **The orbital charge vanishes off the class.** -/
theorem tripticOrbitCharge_ellipticGammaCone_of_notMem {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    {p : ℂ} (hp : ¬ PeriodGroupMem a b p) :
    tripticOrbitCharge (ellipticGammaCone a b) b p = 0 := by
  rw [tripticOrbitCharge]
  have hterm : ∀ m : ℤ, shiftOrder (ellipticGammaCone a b) b (p + (m : ℂ) * b) = 0 := by
    intro m
    have hstep : p + (m : ℂ) * b + b = p + (((m + 1 : ℤ) : ℂ)) * b := by push_cast; ring
    rw [shiftOrder, hstep, meromorphicOrderAt_ellipticGammaCone_orbit_of_notMem ha hb hp,
      meromorphicOrderAt_ellipticGammaCone_orbit_of_notMem ha hb hp]
    simp
  rw [finsum_congr hterm, finsum_zero]

/-! ### The half-line law at an arbitrary period point -/

/-- **The general pole half line.**  Along the `b`-orbit of a period point `c + d·a + e·b`, the cone
product vanishes exactly for `d ≤ 0` and `m ≤ -e`. -/
theorem coneProduct_periodPoint_orbit_eq_zero_iff {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (c d e m : ℤ) :
    coneProduct a b (((c : ℂ) + (d : ℂ) * a + (e : ℂ) * b) + (m : ℂ) * b) = 0
      ↔ (d ≤ 0 ∧ m ≤ -e) := by
  rw [coneProduct_eq_zero_iff' ha hb]
  constructor
  · rintro ⟨j, k, m', hm'⟩
    have hz : ((c - m' : ℤ) : ℂ) + (((j : ℤ) + d) : ℤ) * a + (((k : ℤ) + e + m) : ℤ) * b = 0 := by
      push_cast
      linear_combination hm'
    obtain ⟨-, h2, h3⟩ := hindep _ _ _ hz
    omega
  · rintro ⟨hd, hm⟩
    refine ⟨(-d).toNat, (-(e + m)).toNat, c, ?_⟩
    have hdn : (((-d).toNat : ℕ) : ℤ) = -d := Int.toNat_of_nonneg (by omega)
    have hen : (((-(e + m)).toNat : ℕ) : ℤ) = -(e + m) := Int.toNat_of_nonneg (by omega)
    have hdc : (((-d).toNat : ℕ) : ℂ) = -(d : ℂ) := by exact_mod_cast hdn
    have hec : (((-(e + m)).toNat : ℕ) : ℂ) = -((e : ℂ) + (m : ℂ)) := by exact_mod_cast hen
    rw [hdc, hec]
    ring

/-- **The general zero half line.**  Along the same orbit, the numerator vanishes exactly for
`1 ≤ d` and `1 - e ≤ m`. -/
theorem coneProduct_num_periodPoint_orbit_eq_zero_iff {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (c d e m : ℤ) :
    coneProduct a b (a + b - (((c : ℂ) + (d : ℂ) * a + (e : ℂ) * b) + (m : ℂ) * b)) = 0
      ↔ (1 ≤ d ∧ 1 - e ≤ m) := by
  rw [coneProduct_eq_zero_iff' ha hb]
  constructor
  · rintro ⟨j, k, m', hm'⟩
    have hz : ((-c - m' : ℤ) : ℂ) + (((j : ℤ) + 1 - d) : ℤ) * a
        + (((k : ℤ) + 1 - e - m) : ℤ) * b = 0 := by
      push_cast
      linear_combination hm'
    obtain ⟨-, h2, h3⟩ := hindep _ _ _ hz
    omega
  · rintro ⟨hd, hm⟩
    refine ⟨(d - 1).toNat, (e + m - 1).toNat, -c, ?_⟩
    have hdn : (((d - 1).toNat : ℕ) : ℤ) = d - 1 := Int.toNat_of_nonneg (by omega)
    have hen : (((e + m - 1).toNat : ℕ) : ℤ) = e + m - 1 := Int.toNat_of_nonneg (by omega)
    have hdc : (((d - 1).toNat : ℕ) : ℂ) = (d : ℂ) - 1 := by exact_mod_cast hdn
    have hec : (((e + m - 1).toNat : ℕ) : ℂ) = (e : ℂ) + (m : ℂ) - 1 := by exact_mod_cast hen
    rw [hdc, hec]
    push_cast
    ring

/-- **The order of the elliptic gamma function along the orbit of a period point.** -/
theorem meromorphicOrderAt_ellipticGammaCone_periodPoint {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (c d e m : ℤ) :
    meromorphicOrderAt (ellipticGammaCone a b)
        (((c : ℂ) + (d : ℂ) * a + (e : ℂ) * b) + (m : ℂ) * b)
      = (if 1 ≤ d ∧ 1 - e ≤ m then 1 else 0) - (if d ≤ 0 ∧ m ≤ -e then 1 else 0) := by
  set z : ℂ := ((c : ℂ) + (d : ℂ) * a + (e : ℂ) * b) + (m : ℂ) * b with hz
  have hnum : MeromorphicAt (fun w => coneProduct a b (a + b - w)) z :=
    ((differentiable_ellipticGammaConeNum ha hb).analyticAt z).meromorphicAt
  have hden : MeromorphicAt (coneProduct a b) z :=
    ((differentiable_coneProduct ha hb).analyticAt z).meromorphicAt
  rw [ellipticGammaCone, meromorphicOrderAt_div hnum hden]
  have hnumorder : meromorphicOrderAt (fun w => coneProduct a b (a + b - w)) z
      = if 1 ≤ d ∧ 1 - e ≤ m then 1 else 0 := by
    have han : AnalyticAt ℂ (fun w => coneProduct a b (a + b - w)) z :=
      (differentiable_ellipticGammaConeNum ha hb).analyticAt z
    by_cases hcase : 1 ≤ d ∧ 1 - e ≤ m
    · rw [if_pos hcase, han.meromorphicOrderAt_eq]
      have hval : coneProduct a b (a + b - z) = 0 :=
        (coneProduct_num_periodPoint_orbit_eq_zero_iff ha hb hindep c d e m).mpr hcase
      have hsimple : analyticOrderAt (fun w => coneProduct a b (a + b - w)) z = 1 := by
        obtain ⟨n₀, hn₀⟩ := (coneProduct_eq_zero_iff ha hb (a + b - z)).mp hval
        have huniq : ∀ n : ℕ × ℕ, n ≠ n₀ → coneFactor a b n (a + b - z) ≠ 0 :=
          fun n hn hc => hn (coneFactor_index_unique hindep hc hn₀)
        have hcomp : (fun w => coneProduct a b (a + b - w))
            = (coneProduct a b) ∘ (fun w => a + b - w) := rfl
        rw [hcomp]
        have hderiv : deriv (fun w : ℂ => a + b - w) z = -1 := by
          simp
        rw [analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by
          rw [hderiv]
          norm_num)]
        exact analyticOrderAt_coneProduct_eq_one ha hb hn₀ huniq
      rw [hsimple]
      rfl
    · rw [if_neg hcase, han.meromorphicOrderAt_eq]
      have hval : coneProduct a b (a + b - z) ≠ 0 := fun h =>
        hcase ((coneProduct_num_periodPoint_orbit_eq_zero_iff ha hb hindep c d e m).mp h)
      rw [(analyticOrderAt_eq_zero (𝕜 := ℂ) (E := ℂ)
        (f := fun w : ℂ => coneProduct a b (a + b - w)) (z₀ := z)).mpr (Or.inr hval)]
      rfl
  have hdenorder : meromorphicOrderAt (coneProduct a b) z
      = if d ≤ 0 ∧ m ≤ -e then 1 else 0 := by
    rw [meromorphicOrderAt_coneProduct ha hb hindep]
    by_cases hcase : d ≤ 0 ∧ m ≤ -e
    · rw [if_pos ((coneProduct_periodPoint_orbit_eq_zero_iff ha hb hindep c d e m).mpr hcase),
        if_pos hcase]
    · rw [if_neg (fun h => hcase
        ((coneProduct_periodPoint_orbit_eq_zero_iff ha hb hindep c d e m).mp h)), if_neg hcase]
  rw [hnumorder, hdenorder]

end GaloisForLFunctions.HTGeometry
