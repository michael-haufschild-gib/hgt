import GaloisForLFunctions.HTGeometry.BohrBochnerEquivalence
import GaloisForLFunctions.HTGeometry.BohrMeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Common almost periods, the algebra of almost-periodic functions, and the Bohr spectrum

Two almost-periodic functions have *common* almost periods.  This is the step that Bohr's
relative-density definition cannot see directly and Bochner's compactness form makes immediate: the
pair `t ↦ (f t, g t)` has a totally bounded orbit as soon as both factors do, because a translate of
the pair is determined by a pair of approximating sample times, and there are only finitely many such
pairs.  Translating back through the Bohr criterion produces a single relatively dense set of times
that almost-fixes both functions.

Common almost periods make the almost-periodic functions an algebra, and in particular multiply an
almost-periodic function by a character `t ↦ e^{-iλt}` without leaving the class.  The Bohr
coefficient at the frequency `λ` is then the mean value of that product, the Bohr spectrum is the set
of frequencies with nonzero coefficient, and the frequency module — the object whose rational rank the
finite-phase theorem bounds — is its `ℚ`-span.
-/

open Filter Topology

namespace GaloisForLFunctions

open HTGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Constants are almost periodic. -/
theorem isBohrAlmostPeriodic_const (c : E) : IsBohrAlmostPeriodic (fun _ : ℝ => c) := by
  intro ε hε
  exact ⟨1, one_pos, fun a => ⟨a, ⟨le_refl a, by linarith⟩, fun _ => by simp [hε.le]⟩⟩

/-- A periodic function is almost periodic: the integer multiples of the period are exact periods and
are relatively dense. -/
theorem isBohrAlmostPeriodic_of_periodic {f : ℝ → E} {p : ℝ} (hp : 0 < p)
    (hper : Function.Periodic f p) : IsBohrAlmostPeriodic f := by
  intro ε hε
  refine ⟨p, hp, fun a => ?_⟩
  refine ⟨(⌈a / p⌉ : ℝ) * p, ⟨?_, ?_⟩, fun x => ?_⟩
  · have h := Int.le_ceil (a / p)
    calc a = (a / p) * p := by field_simp
      _ ≤ (⌈a / p⌉ : ℝ) * p := mul_le_mul_of_nonneg_right h hp.le
  · have h := Int.ceil_lt_add_one (a / p)
    calc ((⌈a / p⌉ : ℤ) : ℝ) * p ≤ (a / p + 1) * p := mul_le_mul_of_nonneg_right h.le hp.le
      _ = a + p := by field_simp
  · rw [hper.int_mul ⌈a / p⌉ x, sub_self, norm_zero]
    exact hε.le

/-- **Common approximating sample times.**  If two orbits are totally bounded, so is the orbit of the
pair: each translate is classified by the pair of sample times approximating its two components, and
one representative time per class is enough. -/
theorem hasTotallyBoundedOrbit_prod {f : ℝ → E} {g : ℝ → F}
    (hf : HasTotallyBoundedOrbit f) (hg : HasTotallyBoundedOrbit g) :
    HasTotallyBoundedOrbit (fun t => (f t, g t)) := by
  classical
  intro ε hε
  obtain ⟨Sf, hSfne, hSf⟩ := hf (ε / 2) (by linarith)
  obtain ⟨Sg, hSgne, hSg⟩ := hg (ε / 2) (by linarith)
  choose sf hsfmem hsf using hSf
  choose sg hsgmem hsg using hSg
  -- classify each time by the pair of sample times approximating its two components
  set idx : ℝ → ℝ × ℝ := fun a => (sf a, sg a) with hidx
  set rep : ℝ × ℝ → ℝ := fun q => if h : ∃ a : ℝ, idx a = q then h.choose else 0 with hrep
  refine ⟨(Sf ×ˢ Sg).image rep, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hSfne
    obtain ⟨v, hv⟩ := hSgne
    exact ⟨rep (u, v), Finset.mem_image.mpr ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩⟩
  intro a
  have hex : ∃ b : ℝ, idx b = idx a := ⟨a, rfl⟩
  have hrepa : idx (rep (idx a)) = idx a := by
    rw [hrep]
    simp only [dif_pos hex]
    exact hex.choose_spec
  refine ⟨rep (idx a), Finset.mem_image.mpr
    ⟨idx a, Finset.mem_product.mpr ⟨hsfmem a, hsgmem a⟩, rfl⟩, fun x => ?_⟩
  have hfeq : sf (rep (idx a)) = sf a := congrArg Prod.fst hrepa
  have hgeq : sg (rep (idx a)) = sg a := congrArg Prod.snd hrepa
  have hfb : ‖f (x + a) - f (x + rep (idx a))‖ ≤ ε := by
    have h1 := hsf a x
    have h2 := hsf (rep (idx a)) x
    rw [hfeq] at h2
    calc ‖f (x + a) - f (x + rep (idx a))‖
        = ‖(f (x + a) - f (x + sf a)) + (f (x + sf a) - f (x + rep (idx a)))‖ := by congr 1; abel
      _ ≤ ‖f (x + a) - f (x + sf a)‖ + ‖f (x + sf a) - f (x + rep (idx a))‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := by
          refine add_le_add h1 ?_
          rw [← norm_neg]
          simpa using h2
      _ = ε := by ring
  have hgb : ‖g (x + a) - g (x + rep (idx a))‖ ≤ ε := by
    have h1 := hsg a x
    have h2 := hsg (rep (idx a)) x
    rw [hgeq] at h2
    calc ‖g (x + a) - g (x + rep (idx a))‖
        = ‖(g (x + a) - g (x + sg a)) + (g (x + sg a) - g (x + rep (idx a)))‖ := by congr 1; abel
      _ ≤ ‖g (x + a) - g (x + sg a)‖ + ‖g (x + sg a) - g (x + rep (idx a))‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := by
          refine add_le_add h1 ?_
          rw [← norm_neg]
          simpa using h2
      _ = ε := by ring
  rw [show ((f (x + a), g (x + a)) - (f (x + rep (idx a)), g (x + rep (idx a))))
      = (f (x + a) - f (x + rep (idx a)), g (x + a) - g (x + rep (idx a))) from rfl,
    Prod.norm_mk]
  exact max_le hfb hgb

/-- **Common almost periods.**  Two continuous almost-periodic functions have a relatively dense set
of simultaneous almost periods. -/
theorem isBohrAlmostPeriodic_prod {f : ℝ → E} {g : ℝ → F}
    (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f)
    (hgc : Continuous g) (hga : IsBohrAlmostPeriodic g) :
    IsBohrAlmostPeriodic (fun t => (f t, g t)) :=
  isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit
    (hasTotallyBoundedOrbit_prod (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hfc hfa)
      (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hgc hga))

/-- The simultaneous almost periods, extracted from the pair. -/
theorem exists_common_almostPeriods {f : ℝ → E} {g : ℝ → F}
    (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f)
    (hgc : Continuous g) (hga : IsBohrAlmostPeriodic g) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, ∃ τ ∈ Set.Icc a (a + L),
      (∀ x : ℝ, ‖f (x + τ) - f x‖ ≤ ε) ∧ (∀ x : ℝ, ‖g (x + τ) - g x‖ ≤ ε) := by
  obtain ⟨L, hL, hdense⟩ := isBohrAlmostPeriodic_prod hfc hfa hgc hga ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_, fun x => ?_⟩
  · have := hτ x
    rw [show ((f (x + τ), g (x + τ)) - (f x, g x))
        = (f (x + τ) - f x, g (x + τ) - g x) from rfl, Prod.norm_mk] at this
    exact le_trans (le_max_left _ _) this
  · have := hτ x
    rw [show ((f (x + τ), g (x + τ)) - (f x, g x))
        = (f (x + τ) - f x, g (x + τ) - g x) from rfl, Prod.norm_mk] at this
    exact le_trans (le_max_right _ _) this

/-- The pointwise product of two continuous almost-periodic complex functions is almost periodic. -/
theorem isBohrAlmostPeriodic_mul {f g : ℝ → ℂ}
    (hfc : Continuous f) (hfa : IsBohrAlmostPeriodic f)
    (hgc : Continuous g) (hga : IsBohrAlmostPeriodic g) :
    IsBohrAlmostPeriodic (fun t => f t * g t) := by
  obtain ⟨Cf, hCf⟩ := exists_bound_of_isBohrAlmostPeriodic hfc hfa
  obtain ⟨Cg, hCg⟩ := exists_bound_of_isBohrAlmostPeriodic hgc hga
  have hCf0 : 0 ≤ Cf := le_trans (norm_nonneg _) (hCf 0)
  have hCg0 : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg 0)
  intro ε hε
  have hden : 0 < Cf + Cg + 1 := by linarith
  obtain ⟨L, hL, hdense⟩ :=
    exists_common_almostPeriods hfc hfa hgc hga (ε := ε / (Cf + Cg + 1)) (by positivity)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτf, hτg⟩ := hdense a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have hsplit : f (x + τ) * g (x + τ) - f x * g x
      = (f (x + τ) - f x) * g (x + τ) + f x * (g (x + τ) - g x) := by ring
  have hb1 : ‖(f (x + τ) - f x) * g (x + τ)‖ ≤ (ε / (Cf + Cg + 1)) * Cg := by
    rw [norm_mul]
    exact mul_le_mul (hτf x) (hCg _) (norm_nonneg _) (by positivity)
  have hb2 : ‖f x * (g (x + τ) - g x)‖ ≤ Cf * (ε / (Cf + Cg + 1)) := by
    rw [norm_mul]
    exact mul_le_mul (hCf _) (hτg x) (norm_nonneg _) hCf0
  calc ‖f (x + τ) * g (x + τ) - f x * g x‖
      = ‖(f (x + τ) - f x) * g (x + τ) + f x * (g (x + τ) - g x)‖ := by rw [hsplit]
    _ ≤ ‖(f (x + τ) - f x) * g (x + τ)‖ + ‖f x * (g (x + τ) - g x)‖ := norm_add_le _ _
    _ ≤ (ε / (Cf + Cg + 1)) * Cg + Cf * (ε / (Cf + Cg + 1)) := add_le_add hb1 hb2
    _ ≤ ε := by
        have hkey : (ε / (Cf + Cg + 1)) * Cg + Cf * (ε / (Cf + Cg + 1))
            = ε * ((Cf + Cg) / (Cf + Cg + 1)) := by
          field_simp
          ring
        have hfrac : (Cf + Cg) / (Cf + Cg + 1) ≤ 1 := by
          rw [div_le_one hden]
          linarith
        rw [hkey]
        calc ε * ((Cf + Cg) / (Cf + Cg + 1)) ≤ ε * 1 :=
              mul_le_mul_of_nonneg_left hfrac hε.le
          _ = ε := mul_one ε

/-- The character `t ↦ e^{-iλt}`. -/
noncomputable def bohrChar (lam : ℝ) (t : ℝ) : ℂ :=
  Complex.exp ((-(lam * t) : ℝ) * Complex.I)

theorem continuous_bohrChar (lam : ℝ) : Continuous (bohrChar lam) := by
  unfold bohrChar
  fun_prop

@[simp] theorem norm_bohrChar (lam t : ℝ) : ‖bohrChar lam t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Characters are almost periodic: nonzero frequencies give genuinely periodic characters, and the
zero frequency gives the constant `1`. -/
theorem isBohrAlmostPeriodic_bohrChar (lam : ℝ) : IsBohrAlmostPeriodic (bohrChar lam) := by
  rcases eq_or_ne lam 0 with hlam | hlam
  · subst hlam
    have : bohrChar 0 = fun _ : ℝ => (1 : ℂ) := by
      funext t
      simp [bohrChar]
    rw [this]
    exact isBohrAlmostPeriodic_const 1
  · have hper : Function.Periodic (bohrChar lam) (2 * Real.pi / |lam|) := by
      intro t
      have habs : (0 : ℝ) < |lam| := abs_pos.mpr hlam
      have hstep : ((-(lam * (t + 2 * Real.pi / |lam|)) : ℝ) : ℂ) * Complex.I
          = ((-(lam * t) : ℝ) : ℂ) * Complex.I
            + ((-(lam / |lam|) : ℝ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast
        field_simp
        ring
      rw [bohrChar, bohrChar, hstep, Complex.exp_add]
      have hsign : lam / |lam| = 1 ∨ lam / |lam| = -1 := by
        rcases lt_or_gt_of_ne hlam with h | h
        · right
          rw [abs_of_neg h]
          field_simp
        · left
          rw [abs_of_pos h]
          field_simp
      rcases hsign with h | h <;> rw [h]
      · rw [show ((-(1 : ℝ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
            = ((-1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
          Complex.exp_int_mul_two_pi_mul_I, mul_one]
      · rw [show ((-(-1 : ℝ) : ℝ) : ℂ) * (2 * Real.pi * Complex.I)
            = ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
          Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact isBohrAlmostPeriodic_of_periodic (by positivity) hper

/-- The modulated function `t ↦ f(t) e^{-iλt}` is almost periodic whenever `f` is. -/
theorem isBohrAlmostPeriodic_mul_bohrChar {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : IsBohrAlmostPeriodic f) (lam : ℝ) :
    IsBohrAlmostPeriodic (fun t => f t * bohrChar lam t) :=
  isBohrAlmostPeriodic_mul hfc hfa (continuous_bohrChar lam) (isBohrAlmostPeriodic_bohrChar lam)

/-- **The Bohr coefficient** of `f` at the frequency `λ`: the mean value of `f(t)e^{-iλt}`. -/
noncomputable def bohrCoefficient (f : ℝ → ℂ) (lam : ℝ) : ℂ :=
  bohrMean (fun t => f t * bohrChar lam t)

/-- The Bohr coefficient is the limit of the modulated window averages. -/
theorem tendsto_windowAverage_bohrCoefficient {f : ℝ → ℂ} (hfc : Continuous f)
    (hfa : IsBohrAlmostPeriodic f) (lam : ℝ) :
    Tendsto (windowAverage fun t => f t * bohrChar lam t) atTop
      (nhds (bohrCoefficient f lam)) :=
  tendsto_windowAverage_bohrMean (hfc.mul (continuous_bohrChar lam))
    (isBohrAlmostPeriodic_mul_bohrChar hfc hfa lam)

/-- **The Bohr spectrum** of `f`: the frequencies whose coefficient does not vanish. -/
def bohrSpectrum (f : ℝ → ℂ) : Set ℝ := {lam : ℝ | bohrCoefficient f lam ≠ 0}

/-- **The Bohr frequency module** of `f`: the `ℚ`-span of its spectrum inside `ℝ`.  Its `ℚ`-rank is
the rational rank of the frequency group, the invariant bounded by the finite-phase theorem. -/
noncomputable def bohrFrequencyModule (f : ℝ → ℂ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (bohrSpectrum f)

theorem subset_bohrFrequencyModule (f : ℝ → ℂ) :
    bohrSpectrum f ⊆ (bohrFrequencyModule f : Set ℝ) :=
  Submodule.subset_span

/-- A frequency outside the module has vanishing coefficient. -/
theorem bohrCoefficient_eq_zero_of_notMem {f : ℝ → ℂ} {lam : ℝ}
    (h : lam ∉ bohrFrequencyModule f) : bohrCoefficient f lam = 0 := by
  by_contra hne
  exact h (subset_bohrFrequencyModule f hne)

end GaloisForLFunctions
