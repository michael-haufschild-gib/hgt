import GaloisForLFunctions.HTGeometry.OrbitExceptionalTimes
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Half-period deletion bounds sign intervals

Positive translations by the half-periods annihilate a finite trigonometric
sum. Their support diameter bounds every interval on which a nonzero sum
has one sign. No separation between frequencies is required.
-/

open Filter Topology Set
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Product of the positive translation operators `1 + τ_h`. -/
def halfShiftSum : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f, t => f t
  | h :: l, f, t => halfShiftSum l f t + halfShiftSum l f (t + h)

@[simp] theorem halfShiftSum_zero (l : List ℝ) (t : ℝ) :
    halfShiftSum l (fun _ => 0) t = 0 := by
  induction l generalizing t with
  | nil => rfl
  | cons h l ih => simp only [halfShiftSum, ih, add_zero]

/-- Positive deletion commutes with finite superposition. -/
theorem halfShiftSum_sum {ι : Type*} (l : List ℝ) (S : Finset ι)
    (f : ι → ℝ → ℝ) (t : ℝ) :
    halfShiftSum l (fun u => ∑ i ∈ S, f i u) t =
      ∑ i ∈ S, halfShiftSum l (f i) t := by
  induction l generalizing t with
  | nil => rfl
  | cons h l ih => simp only [halfShiftSum, ih, Finset.sum_add_distrib]

private theorem halfShiftSum_antiperiod (l : List ℝ) {f : ℝ → ℝ} {h : ℝ}
    (hf : ∀ t, f (t + h) = -f t) (t : ℝ) :
    halfShiftSum l f (t + h) = -halfShiftSum l f t := by
  induction l generalizing t with
  | nil => exact hf t
  | cons k l ih =>
      change halfShiftSum l f (t + h) + halfShiftSum l f (t + h + k) = _
      rw [show t + h + k = (t + k) + h by ring, ih, ih]
      change -halfShiftSum l f t + -halfShiftSum l f (t + k) =
        -(halfShiftSum l f t + halfShiftSum l f (t + k))
      ring

/-- One matching half-period annihilates its mode, regardless of the other shifts. -/
theorem halfShiftSum_eq_zero_of_antiperiod {l : List ℝ} {f : ℝ → ℝ} {h : ℝ}
    (hh : h ∈ l) (hf : ∀ t, f (t + h) = -f t) (t : ℝ) :
    halfShiftSum l f t = 0 := by
  induction l generalizing t with
  | nil => simp only [List.not_mem_nil] at hh
  | cons k l ih =>
      rcases List.mem_cons.mp hh with rfl | hh
      · rw [halfShiftSum, halfShiftSum_antiperiod l hf, add_neg_cancel]
      · simp only [halfShiftSum, ih hh, add_zero]

/-- On the support interval, deletion preserves nonnegativity and includes the original value. -/
theorem le_halfShiftSum_of_nonneg {l : List ℝ} (hl : ∀ h ∈ l, 0 ≤ h)
    {f : ℝ → ℝ} {t : ℝ} (hf : ∀ u ∈ Icc t (t + l.sum), 0 ≤ f u) :
    0 ≤ halfShiftSum l f t ∧ f t ≤ halfShiftSum l f t := by
  induction l generalizing t with
  | nil => exact ⟨hf t ⟨le_rfl, by simpa only [List.sum_nil, add_zero] using (le_rfl : t ≤ t)⟩, le_rfl⟩
  | cons h l ih =>
      have hh : 0 ≤ h := hl h (List.mem_cons_self ..)
      have htail : ∀ k ∈ l, 0 ≤ k := fun k hk => hl k (List.mem_cons_of_mem _ hk)
      have hleft := ih htail (t := t) (fun u hu => hf u
        ⟨hu.1, by simp only [List.sum_cons]; linarith only [hu.2, hh]⟩)
      have hright := ih htail (t := t + h) (fun u hu => hf u
        ⟨by linarith only [hu.1, hh], by simp only [List.sum_cons]; linarith only [hu.2]⟩)
      exact ⟨add_nonneg hleft.1 hright.1,
        hleft.2.trans (le_add_of_nonneg_right hright.1)⟩

/-- A nonzero analytic function annihilated by positive shifts cannot keep one sign
on an interval longer than their total displacement. -/
theorem length_le_sum_of_halfShiftSum_zero {l : List ℝ}
    (hl : ∀ h ∈ l, 0 ≤ h) {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f univ) (hne : ∃ t, f t ≠ 0)
    (hkill : ∀ t, halfShiftSum l f t = 0) {a L : ℝ}
    (hpos : ∀ t ∈ Icc a (a + L), 0 ≤ f t) : L ≤ l.sum := by
  by_contra h
  have hlen : l.sum < L := lt_of_not_ge h
  have hsum : 0 ≤ l.sum := List.sum_nonneg hl
  have hzero : ∀ t ∈ Ioo a (a + L - l.sum), f t = 0 := by
    intro t ht
    have hlocal : ∀ u ∈ Icc t (t + l.sum), 0 ≤ f u := by
      intro u hu
      exact hpos u ⟨ht.1.le.trans hu.1, by linarith only [hu.2, ht.2]⟩
    have hbound := (le_halfShiftSum_of_nonneg hl hlocal).2
    rw [hkill] at hbound
    exact le_antisymm hbound (hlocal t ⟨le_rfl, by linarith only [hsum]⟩)
  let m := (a + (a + L - l.sum)) / 2
  have ham : a < m := by dsimp [m]; linarith only [hlen]
  have hmb : m < a + L - l.sum := by dsimp [m]; linarith only [hlen]
  have hevent : f =ᶠ[𝓝 m] 0 := by
    filter_upwards [Ioo_mem_nhds ham hmb] with t ht
    exact hzero t ht
  have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ m) hevent
  obtain ⟨t, ht⟩ := hne
  exact ht (hall (mem_univ t))

/-- The sum of half-periods bounds a sign interval of any nonzero real trigonometric sum. -/
theorem sign_interval_le_sum_halfPeriods {n : ℕ} (a b γ : Fin n → ℝ)
    (hγ : ∀ j, 0 < γ j)
    (hne : ∃ t, (∑ j, (a j * Real.cos (γ j * t) + b j * Real.sin (γ j * t))) ≠ 0)
    {x L : ℝ}
    (hpos : ∀ t ∈ Icc x (x + L),
      0 ≤ ∑ j, (a j * Real.cos (γ j * t) + b j * Real.sin (γ j * t))) :
    L ≤ ∑ j, Real.pi / γ j := by
  classical
  let l := (Finset.univ : Finset (Fin n)).toList.map (fun j => Real.pi / γ j)
  have hl : ∀ h ∈ l, 0 ≤ h := by
    intro h hh
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hh
    exact div_nonneg Real.pi_pos.le (hγ j).le
  have hkill : ∀ t, halfShiftSum l
      (fun u => ∑ j, (a j * Real.cos (γ j * u) + b j * Real.sin (γ j * u))) t = 0 := by
    intro t
    rw [halfShiftSum_sum]
    apply Finset.sum_eq_zero
    intro j _
    apply halfShiftSum_eq_zero_of_antiperiod (h := Real.pi / γ j)
    · exact List.mem_map.mpr ⟨j, by simp, rfl⟩
    · intro u
      have hangle : γ j * (u + Real.pi / γ j) = γ j * u + Real.pi := by
        field_simp [(hγ j).ne']
      rw [hangle, Real.cos_add_pi, Real.sin_add_pi]
      ring
  have hbound := length_le_sum_of_halfShiftSum_zero hl
    (GaloisForLFunctions.HTGeometry.analyticOnNhd_trigSum a b γ) hne hkill hpos
  simpa only [l, Finset.sum_map_toList] using hbound

/-- Frequencies above `Γ` force a sign change within `nπ/Γ`, without a separation hypothesis. -/
theorem sign_interval_resolution {n : ℕ} (a b γ : Fin n → ℝ) {Γ : ℝ}
    (hΓ : 0 < Γ) (hγ : ∀ j, Γ ≤ γ j)
    (hne : ∃ t, (∑ j, (a j * Real.cos (γ j * t) + b j * Real.sin (γ j * t))) ≠ 0)
    {x L : ℝ}
    (hpos : ∀ t ∈ Icc x (x + L),
      0 ≤ ∑ j, (a j * Real.cos (γ j * t) + b j * Real.sin (γ j * t))) :
    Γ * L ≤ n * Real.pi := by
  have hbound := sign_interval_le_sum_halfPeriods a b γ
    (fun j => hΓ.trans_le (hγ j)) hne hpos
  have hsum : (∑ j, Real.pi / γ j) ≤ n * (Real.pi / Γ) := by
    calc (∑ j, Real.pi / γ j) ≤ ∑ _j : Fin n, Real.pi / Γ :=
        Finset.sum_le_sum (fun j _ => div_le_div_of_nonneg_left Real.pi_pos.le hΓ (hγ j))
      _ = n * (Real.pi / Γ) := by simp
  have hh := mul_le_mul_of_nonneg_left (hbound.trans hsum) hΓ.le
  calc Γ * L ≤ Γ * (n * (Real.pi / Γ)) := hh
    _ = n * Real.pi := by field_simp

#print axioms length_le_sum_of_halfShiftSum_zero
#print axioms sign_interval_le_sum_halfPeriods
#print axioms sign_interval_resolution

/-- Real part of a finite exponential sum, in sine and cosine coordinates. -/
theorem re_exponentialSum_eq_trigSum {n : ℕ} (a : Fin n → ℂ) (γ : Fin n → ℝ) (t : ℝ) :
    (∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re =
      ∑ j, ((a j).re * Real.cos (γ j * t) + (-(a j).im) * Real.sin (γ j * t)) := by
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- A nonzero real trace of `n` positive-frequency modes cannot remain nonnegative
on an interval longer than `nπ/Γ`. -/
theorem exponentialSum_sign_interval_resolution {n : ℕ} (a : Fin n → ℂ) (γ : Fin n → ℝ)
    {Γ : ℝ} (hΓ : 0 < Γ) (hγ : ∀ j, Γ ≤ γ j)
    (hne : ∃ t, (∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re ≠ 0)
    {x L : ℝ}
    (hpos : ∀ t ∈ Icc x (x + L),
      0 ≤ (∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re) :
    Γ * L ≤ n * Real.pi := by
  apply sign_interval_resolution (fun j => (a j).re) (fun j => -(a j).im) γ hΓ hγ
  · simpa only [re_exponentialSum_eq_trigSum] using hne
  · simpa only [re_exponentialSum_eq_trigSum] using hpos

#print axioms exponentialSum_sign_interval_resolution

/-- Without a nonvanishing premise, the exact alternative is a short sign interval
or an identically zero real trace. -/
theorem exponentialSum_sign_interval_short_or_zero {n : ℕ}
    (a : Fin n → ℂ) (γ : Fin n → ℝ) {Γ : ℝ} (hΓ : 0 < Γ) (hγ : ∀ j, Γ ≤ γ j)
    {x L : ℝ}
    (hpos : ∀ t ∈ Icc x (x + L),
      0 ≤ (∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re) :
    Γ * L ≤ n * Real.pi ∨
      ∀ t, (∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re = 0 := by
  classical
  by_cases hne : ∃ t, (∑ j, a j * Complex.exp (((γ j * t : ℝ) : ℂ) * Complex.I)).re ≠ 0
  · exact Or.inl (exponentialSum_sign_interval_resolution a γ hΓ hγ hne hpos)
  · exact Or.inr (fun t => by_contra fun ht => hne ⟨t, ht⟩)

#print axioms exponentialSum_sign_interval_short_or_zero

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
