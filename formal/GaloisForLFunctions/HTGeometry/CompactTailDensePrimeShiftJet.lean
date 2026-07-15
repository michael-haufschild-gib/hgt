import GaloisForLFunctions.HTGeometry.CompactTailDenseAsymptoticScale
import GaloisForLFunctions.HTGeometry.PrimeExpLogFiberRigidity
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Compact tail-dense prime shift--jet separation

Prime Dirichlet shifts of distinct real parts, ordered first by exponential decay and then by
logarithmic degree, form a cofinite asymptotic scale. The general tail-dense tensor-separation law
therefore makes every finite source--shift--jet rectangle independent modulo finite prime support.

Unlike the recurrent-fibre theorem, this result requires no repeated coefficient value and no
rate of equidistribution. Every point of the constraint geometry need only remain a cluster point
after arbitrary finite deletion.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

private def primeSubtypeEmbedding : Nat.Primes ↪ ℕ :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- Prime values escape every real bound along the cofinite filter on the prime subtype. -/
theorem tendsto_primeReal_cofinite_atTop :
    Tendsto (fun p : Nat.Primes => (p : ℝ)) cofinite atTop := by
  apply Filter.tendsto_atTop.mpr
  intro b
  rw [eventually_cofinite]
  apply (Set.Finite.preimage_embedding primeSubtypeEmbedding
    (Set.finite_lt_nat ⌈b⌉₊)).subset
  intro p hp
  change (p : ℕ) < ⌈b⌉₊
  rw [Nat.lt_ceil]
  exact lt_of_not_ge hp

/-- The real prime logarithm tends to infinity on the cofinite prime filter. -/
theorem tendsto_primeRealLog_cofinite_atTop :
    Tendsto (fun p : Nat.Primes => Real.log (p : ℝ)) cofinite atTop := by
  simpa only [Function.comp_apply] using
    Real.tendsto_log_atTop.comp tendsto_primeReal_cofinite_atTop

/-- A strictly lower logarithmic degree is asymptotically negligible. -/
theorem tendsto_primeLogClock_pow_div_pow_of_lt {k l : ℕ} (hkl : k < l) :
    Tendsto (fun p : Nat.Primes => primeLogClock p ^ k / primeLogClock p ^ l)
      cofinite (𝓝 0) := by
  have hreal : Tendsto
      (fun p : Nat.Primes => Real.log (p : ℝ) ^ k / Real.log (p : ℝ) ^ l)
      cofinite (𝓝 0) :=
    (tendsto_pow_div_pow_atTop_zero hkl).comp tendsto_primeRealLog_cofinite_atTop
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  convert hcomplex using 1
  funext p
  change ((Real.log (p : ℝ) : ℂ) ^ k / (Real.log (p : ℝ) : ℂ) ^ l) =
    ((Real.log (p : ℝ) ^ k / Real.log (p : ℝ) ^ l : ℝ) : ℂ)
  push_cast
  rfl

/-- A shift with larger real part is asymptotically negligible relative to one with smaller real
part, regardless of the two fixed logarithmic degrees. -/
theorem tendsto_primeShiftLog_ratio_of_re_lt
    {α β : ℂ} (hβα : β.re < α.re) (k l : ℕ) :
    Tendsto (fun p : Nat.Primes =>
      (primeShiftFactor α p * primeLogClock p ^ k) /
        (primeShiftFactor β p * primeLogClock p ^ l))
      cofinite (𝓝 0) := by
  let δ : ℝ := α.re - β.re
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hmajor : Tendsto (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ k * Real.exp (-(δ * Real.log (p : ℝ))))
      cofinite (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_mul hδ k).comp tendsto_primeRealLog_cofinite_atTop
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [tendsto_primeRealLog_cofinite_atTop.eventually_ge_atTop 1] with p hp
  let L : ℝ := Real.log (p : ℝ)
  have hL0 : 0 < L := zero_lt_one.trans_le hp
  have hnormClock : ‖primeLogClock p‖ = L := by
    change ‖(L : ℂ)‖ = L
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
  have hnormShift : ∀ γ : ℂ, ‖primeShiftFactor γ p‖ = Real.exp (-γ.re * L) := by
    intro γ
    rw [primeShiftFactor, Complex.norm_exp]
    congr 1
    change (-γ * (L : ℂ)).re = _
    simp
  have hden : 1 ≤ L ^ l := one_le_pow₀ hp
  have hrewrite :
      (Real.exp (-α.re * L) * L ^ k) /
          (Real.exp (-β.re * L) * L ^ l) =
        (L ^ k * Real.exp (-(δ * L))) / L ^ l := by
    have hE : Real.exp (-β.re * L) ≠ 0 := (Real.exp_pos _).ne'
    have hLn : L ^ l ≠ 0 := pow_ne_zero _ hL0.ne'
    field_simp
    rw [← Real.exp_add]
    congr 1
    dsimp [δ]
    ring
  change ‖(primeShiftFactor α p * primeLogClock p ^ k) /
      (primeShiftFactor β p * primeLogClock p ^ l)‖ ≤
    L ^ k * Real.exp (-(δ * L))
  simp only [norm_div, norm_mul, norm_pow, hnormShift, hnormClock]
  rw [hrewrite]
  exact div_le_self (mul_nonneg (pow_nonneg hL0.le k) (Real.exp_pos _).le) hden

/-- The prime shift--logarithm weight indexed by a shift and a finite jet degree. -/
def primeShiftLogWeight {A : Type*} (alpha : A → ℂ) (m : ℕ)
    (ak : A × Fin (m + 1)) (p : Nat.Primes) : ℂ :=
  primeShiftFactor (alpha ak.1) p * primeLogClock p ^ (ak.2 : ℕ)

/-- Distinct real shift parts and logarithmic degree order the prime weights into a complete
cofinite asymptotic scale. -/
theorem primeShiftLogWeight_cofiniteAsymptoticScale
    {A : Type*} [Fintype A] (alpha : A → ℂ)
    (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    CofiniteAsymptoticScale (primeShiftLogWeight alpha m) := by
  classical
  constructor
  · intro ak p
    have hp1 : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast p.2.one_lt
    have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos hp1).ne'
    exact mul_ne_zero (primeShiftFactor_ne_zero _ _) (pow_ne_zero _ (by
      change (Real.log (p : ℝ) : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr hlog))
  · intro s hs
    obtain ⟨akMin, hakMin, hmin⟩ :=
      Finset.exists_min_image s (fun ak => (alpha ak.1).re) hs
    let same : Finset (A × Fin (m + 1)) := s.filter fun ak => ak.1 = akMin.1
    have hsame : same.Nonempty := by
      exact ⟨akMin, Finset.mem_filter.mpr ⟨hakMin, rfl⟩⟩
    obtain ⟨ak₀, hak₀same, hkmax⟩ :=
      Finset.exists_max_image same (fun ak => (ak.2 : ℕ)) hsame
    have hak₀ : ak₀ ∈ s := (Finset.mem_filter.mp hak₀same).1
    have ha₀ : ak₀.1 = akMin.1 := (Finset.mem_filter.mp hak₀same).2
    refine ⟨ak₀, hak₀, ?_⟩
    intro ak hak hakne
    by_cases ha : ak.1 = ak₀.1
    · have haksame : ak ∈ same := by
        apply Finset.mem_filter.mpr
        exact ⟨hak, ha.trans ha₀⟩
      have hkle : (ak.2 : ℕ) ≤ (ak₀.2 : ℕ) := hkmax ak haksame
      have hklt : (ak.2 : ℕ) < (ak₀.2 : ℕ) := by
        rcases hkle.eq_or_lt with heq | hlt
        · have hak2 : ak.2 = ak₀.2 := Fin.ext heq
          exact (hakne (Prod.ext ha hak2)).elim
        · exact hlt
      have heq : (fun p : Nat.Primes =>
          primeShiftLogWeight alpha m ak p / primeShiftLogWeight alpha m ak₀ p) =
          fun p => primeLogClock p ^ (ak.2 : ℕ) /
            primeLogClock p ^ (ak₀.2 : ℕ) := by
        funext p
        simp only [primeShiftLogWeight, ha]
        field_simp [primeShiftFactor_ne_zero]
      rw [heq]
      exact tendsto_primeLogClock_pow_div_pow_of_lt hklt
    · have hrealne : (alpha ak.1).re ≠ (alpha ak₀.1).re := fun h =>
        ha (hdistinct h)
      have hle : (alpha akMin.1).re ≤ (alpha ak.1).re := hmin ak hak
      have hlt : (alpha ak₀.1).re < (alpha ak.1).re := by
        rw [ha₀]
        exact lt_of_le_of_ne hle (by simpa [ha₀] using hrealne.symm)
      exact tendsto_primeShiftLog_ratio_of_re_lt hlt _ _

/-- **Compact tail-dense prime shift--jet law.** Every finite family of continuous independent
constraint observables remains independent modulo finite prime support after adjoining any finite
palette of Dirichlet shifts with distinct real parts and any finite logarithmic jet rectangle. -/
theorem cofiniteTailDenseOn_primeShiftLogJet_tailIndependent
    {V J A : Type*} [TopologicalSpace V] [Fintype J] [Fintype A]
    (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j => fun v : K => f j v.1))
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re))
    (m : ℕ) :
    TailCoefficientIndependent
      (fun jak : J × (A × Fin (m + 1)) => fun p =>
        f jak.1 (x p) * primeShiftFactor (alpha jak.2.1) p *
          primeLogClock p ^ (jak.2.2 : ℕ)) := by
  have h := cofiniteTailDenseOn_asymptoticScale_tensor_tailIndependent
    x K hx f hf hlinear (primeShiftLogWeight alpha m)
      (primeShiftLogWeight_cofiniteAsymptoticScale alpha hdistinct m)
  simpa only [primeShiftLogWeight, mul_assoc] using h

/-- Prime-power valuation dilation and the rotated analytic clock only rescale the columns of the
tail-dense shift--jet rectangle by nonzero constants, so the complete separation law survives in
the exact coefficient form used by the arithmetic differential carriers. -/
theorem cofiniteTailDenseOn_primePowerShiftedRotatedJet_tailIndependent
    {V J A : Type*} [TopologicalSpace V] [Fintype J] [Fintype A]
    (e : ℕ) (x : Nat.Primes → V) (K : Set V) (hx : CofiniteTailDenseOn x K)
    (f : J → V → ℂ) (hf : ∀ j, Continuous (f j))
    (hlinear : LinearIndependent ℂ (fun j => fun v : K => f j v.1))
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re))
    (m : ℕ) :
    TailCoefficientIndependent
      (fun jak : J × (A × Fin (m + 1)) => fun p =>
        f jak.1 (x p) * primeShiftFactor (alpha jak.2.1) p *
          ((((e + 1 : ℕ) : ℂ) * rotatedPrimeLogClock p) ^
            (jak.2.2 : ℕ))) := by
  classical
  let raw : J × (A × Fin (m + 1)) → Nat.Primes → ℂ := fun jak p =>
    f jak.1 (x p) * primeShiftFactor (alpha jak.2.1) p *
      primeLogClock p ^ (jak.2.2 : ℕ)
  let u : J × (A × Fin (m + 1)) → ℂ := fun jak =>
    ((((e + 1 : ℕ) : ℂ) * Complex.I) ^ (jak.2.2 : ℕ))
  have hu : ∀ jak, u jak ≠ 0 := by
    intro jak
    apply pow_ne_zero
    exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero e) Complex.I_ne_zero
  have hraw : TailCoefficientIndependent raw := by
    simpa only [raw] using
      cofiniteTailDenseOn_primeShiftLogJet_tailIndependent
        x K hx f hf hlinear alpha hdistinct m
  have hscaled : TailCoefficientIndependent (fun jak p => u jak * raw jak p) :=
    (tailCoefficientIndependent_scale_columns_iff raw u hu).mpr hraw
  convert hscaled using 1
  funext jak p
  simp only [u, raw, rotatedPrimeLogClock, mul_pow]
  ring

end

end GaloisForLFunctions.HTGeometry
