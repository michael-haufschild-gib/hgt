import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MaximalBlindIdealOfTheMeyerSource
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerNumericalRadicalAndMultiplicity
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogOperatorContinuity
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGaussianSourceApproximation
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGeneralizedZeroJetDescent
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.HTGeometry.TailCanonicalProducts

/-!
# Spectral synthesis in the blind ideal

In the natural Fréchet topology of the Meyer source, every subspace cut out by vanishing orders at
the Xi divisor is the closed span of the jet sources it contains together with the Poisson
boundary `R` (the sources whose Mellin transform vanishes to full multiplicity at every Xi zero).

For `k : XiDivisorSupport → ℕ` let `I_k` be the sources whose Mellin transform has its jets of
order `< k ρ` zero at every `ρ`, and `E_k` the span of the jet sources `e_{ρ,j}` with `k ρ ≤ j`.

* **Synthesis** (`closure_orderJetSpan_sup_poissonBoundary`): `closure (E_k ⊔ R) = I_k`.
* **Critical jets** (`closure_criticalJetSpan_sup_poissonBoundary`): the closure of the critical
  jet sources plus `R` is the full-jet blind ideal, the sources with every off-line jet zero.
* **The value-blind ideal** (`closure_valueBlindJetSpan_sup_poissonBoundary`):
  `meyerTraceBoundedIdeal` is the closure of the critical jet sources, the off-line jet sources of
  positive order, and `R`.
* **Simplicity** (`closure_criticalJetSpan_sup_eq_meyerTraceBoundedIdeal_iff`): the critical jet
  sources and `R` are dense in `meyerTraceBoundedIdeal` iff every off-line zero is simple.
* **Exhaustion** (`closure_criticalJetSpan_sup_poissonBoundary_eq_univ_iff`): they are dense in the
  whole source iff RH.

Mechanism. Gaussian damping `e^{εs²}` is removed in the limit (`deningerMeyerGaussianSource_tendsto`).
For a damped source, multiply its Mellin transform by the tail `P_F(s) = ∏_{ρ ∉ F} E₁(z/z_ρ)`,
`z = (s − ½)(−i)`, of the canonical product of `ξ` over the zeros outside a finite set `F`. The tail
kills every jet outside `F`; finitely many jet sources repair the jets in `F`; the remainder lies in
`R`. The tails satisfy `‖P_F(z)‖ ≤ C e^{δ‖z‖²}` uniformly in `F`, so `e^{εs²}` dominates them on
every vertical line, and `P_F → 1` pointwise; dominated convergence on vertical Mellin lines then
controls every weighted derivative gauge.
-/

open Complex Filter Topology Set MeasureTheory
open RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open ArithmeticCastelnuovoSeveri
open scoped DeningerMeyerNaturalTopology

/-! ### 1. Divisor-order ideals and jet spans -/

/-- Sources whose Mellin transform has zero jets of every order `< k ρ` (below the multiplicity)
at every Xi zero `ρ`. -/
def divisorOrderIdeal (k : XiDivisorSupport → ℕ) :
    Submodule ℂ DeningerMeyerStrongLogTarget where
  carrier := {g | ∀ (ρ : XiDivisorSupport) (j : DeningerArithmeticJetIndex ρ), j.val < k ρ →
    deningerMeyerStrongLogMellinJetLM j.val (ρ : ℂ) g = 0}
  zero_mem' := fun ρ j _ => map_zero _
  add_mem' := fun hf hg ρ j hj => by rw [map_add, hf ρ j hj, hg ρ j hj, add_zero]
  smul_mem' := fun c _ hg ρ j hj => by rw [map_smul, hg ρ j hj, smul_zero]

/-- The jet sources of order at least `k ρ`: exactly those lying in `divisorOrderIdeal k`. -/
def orderJetSpan (k : XiDivisorSupport → ℕ) : Submodule ℂ DeningerMeyerStrongLogTarget :=
  Submodule.span ℂ {g | ∃ (ρ : XiDivisorSupport) (j : DeningerArithmeticJetIndex ρ),
    k ρ ≤ j.val ∧ g = meyerSingleJetSource ρ j}

/-- The Poisson boundary: sources with every divisor jet zero. -/
abbrev poissonBoundary : Submodule ℂ DeningerMeyerStrongLogTarget :=
  LinearMap.range deningerMeyerStrongLogSumLM

theorem isClosed_divisorOrderIdeal (k : XiDivisorSupport → ℕ) :
    IsClosed (divisorOrderIdeal k : Set DeningerMeyerStrongLogTarget) := by
  have e : (divisorOrderIdeal k : Set DeningerMeyerStrongLogTarget) =
      ⋂ (ρ : XiDivisorSupport) (j : DeningerArithmeticJetIndex ρ) (_ : j.val < k ρ),
        (deningerMeyerStrongLogMellinJetLM j.val (ρ : ℂ)) ⁻¹' {0} := by
    ext g
    simp only [SetLike.mem_coe, mem_iInter, mem_preimage, mem_singleton_iff]
    rfl
  rw [e]
  exact isClosed_iInter fun ρ => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (deningerMeyerStrongLogMellinJetLM_continuous _ _)

theorem orderJetSpan_sup_poissonBoundary_le (k : XiDivisorSupport → ℕ) :
    orderJetSpan k ⊔ poissonBoundary ≤ divisorOrderIdeal k := by
  refine sup_le (Submodule.span_le.mpr ?_) fun g hg σ i _ => ?_
  · rintro _ ⟨ρ, j, hkj, rfl⟩ σ i hi
    rw [meyerSingleJetSource_jet, if_neg]
    rintro ⟨rfl, hij⟩
    omega
  · exact (meyerSource_boundary_iff_jets_zero g).mp hg σ i

/-! ### 2. Damped tail data -/

/-- The centered spectral coordinate `z = (s − ½)(−i)` of a Mellin point. -/
def spectralCoordinate (s : ℂ) : ℂ := (s - 1 / 2) * (-I)

theorem norm_spectralCoordinate_sq (s : ℂ) :
    ‖spectralCoordinate s‖ ^ (2 : ℕ) = (s.re - 1 / 2) ^ 2 + s.im ^ 2 := by
  rw [spectralCoordinate, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [sub_re, sub_im, div_ofNat_re, div_ofNat_im, one_re, one_im, zero_div, sub_zero]
  ring

/-- The multiplicity copies of the zeros in a finite support set. -/
def supportCopies (F : Finset XiDivisorSupport) : Finset XiZeroCopy :=
  F.sigma fun _ => Finset.univ

theorem mem_supportCopies {F : Finset XiDivisorSupport} {q : XiZeroCopy} :
    q ∈ supportCopies F ↔ q.1 ∈ F := by
  simp [supportCopies]

theorem tendsto_supportCopies :
    Tendsto supportCopies (atTop : Filter (Finset XiDivisorSupport)) atTop := by
  classical
  refine tendsto_atTop_atTop.mpr fun T => ⟨T.image Sigma.fst, fun F hF q hq => ?_⟩
  exact mem_supportCopies.mpr (hF (Finset.mem_image_of_mem _ hq))

/-- The tail of the canonical product of `ξ` over the zeros outside `F`, in the Mellin variable. -/
def xiTail (F : Finset XiDivisorSupport) (s : ℂ) : ℂ :=
  canonicalProductE1Tail xiSpectralPoint (supportCopies F) (spectralCoordinate s)

theorem differentiable_xiTail (F : Finset XiDivisorSupport) : Differentiable ℂ (xiTail F) :=
  (canonicalProductE1Tail_differentiable xiSpectralPoint xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable _).comp (by unfold spectralCoordinate; fun_prop)

theorem tendsto_xiTail_one (s : ℂ) :
    Tendsto (fun F : Finset XiDivisorSupport => xiTail F s) atTop (𝓝 1) :=
  (tendsto_canonicalProductE1Tail_one xiSpectralPoint xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable (spectralCoordinate s)).comp tendsto_supportCopies

/-- **Half-Gaussian domination of the tails.** On every vertical strip, `e^{εs²/2}` times any tail
is bounded by one constant, uniformly in `F`. -/
theorem exists_halfGaussian_xiTail_le {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Finset XiDivisorSupport) (s : ℂ), a ≤ s.re → s.re ≤ b →
      ‖Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2) * xiTail F s‖ ≤ C := by
  obtain ⟨C₀, hC₀, hC⟩ := exists_norm_canonicalProductE1Tail_le xiSpectralPoint
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable (δ := ε / 4) (by positivity)
  set A : ℝ := |a| + |b|
  refine ⟨C₀ * Real.exp (ε / 2 * A ^ 2 + ε / 4 * (A + 1 / 2) ^ 2), by positivity,
    fun F s ha hb => ?_⟩
  have hre : |s.re| ≤ A := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b]
  have hA : 0 ≤ A := by positivity
  have hsq : s.re ^ 2 ≤ A ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg s.re) hre 2
  have hsq' : (s.re - 1 / 2) ^ 2 ≤ (A + 1 / 2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by norm_num; linarith)) 2
  have hexp : ‖Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2)‖ =
      Real.exp (ε / 2 * (s.re ^ 2 - s.im ^ 2)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re, Complex.mul_im]
  rw [norm_mul, hexp]
  calc Real.exp (ε / 2 * (s.re ^ 2 - s.im ^ 2)) * ‖xiTail F s‖
      ≤ Real.exp (ε / 2 * (s.re ^ 2 - s.im ^ 2)) *
          (C₀ * Real.exp (ε / 4 * ((s.re - 1 / 2) ^ 2 + s.im ^ 2))) := by
        gcongr
        rw [← norm_spectralCoordinate_sq]
        exact hC _ _
    _ = C₀ * Real.exp (ε / 2 * s.re ^ 2 + ε / 4 * (s.re - 1 / 2) ^ 2 - ε / 4 * s.im ^ 2) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
    _ ≤ _ := by
        gcongr
        nlinarith [sq_nonneg s.im]

/-- An entire function bounded on vertical strips preserves Mellin regularity. -/
theorem mellinRegular_mul_bounded {G H : ℂ → ℂ}
    (hG : DeningerEntireMellinRegular G) (hH : Differentiable ℂ H)
    (hb : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖H s‖ ≤ C) :
    DeningerEntireMellinRegular (fun s => G s * H s) := by
  intro α β
  refine ⟨fun s h₁ h₂ => ((hG α β).diff s h₁ h₂).mul (hH s), fun a b ha hb' K => ?_⟩
  obtain ⟨C₁, h₁⟩ := (hG α β).decay a b ha hb' K
  obtain ⟨C₂, hC₂, h₂⟩ := hb a b
  refine ⟨C₁ * C₂, fun s hsa hsb => ?_⟩
  rw [norm_mul, mul_div_right_comm]
  exact mul_le_mul (h₁ s hsa hsb) (h₂ s hsa hsb) (norm_nonneg _)
    ((norm_nonneg _).trans (h₁ s hsa hsb))

/-- The damped tail datum `e^{εs²} ĝ(s) P_F(s)`. -/
def dampedTailDatum (g : DeningerMeyerStrongLogTarget) (ε : ℝ) (F : Finset XiDivisorSupport)
    (s : ℂ) : ℂ :=
  Complex.exp ((ε : ℂ) * s ^ 2) * deningerMeyerStrongLogMellin g s * xiTail F s

theorem dampedTailDatum_eq_halves (g : DeningerMeyerStrongLogTarget) (ε : ℝ)
    (F : Finset XiDivisorSupport) (s : ℂ) :
    dampedTailDatum g ε F s =
      deningerGaussianMellinRegularization (ε / 2) (deningerMeyerStrongLogMellin g) s *
        (Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2) * xiTail F s) := by
  have he : Complex.exp ((ε : ℂ) * s ^ 2) =
      Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2) * Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [dampedTailDatum, deningerGaussianMellinRegularization, he]
  ring

theorem dampedTailDatum_entireRegular (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε)
    (F : Finset XiDivisorSupport) :
    DeningerEntireMellinRegular (dampedTailDatum g ε F) := by
  have h := mellinRegular_mul_bounded (deningerMeyerStrongLogMellin_gaussianRegular g (half_pos hε))
    (H := fun s => Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2) * xiTail F s)
    ((by fun_prop : Differentiable ℂ fun s : ℂ => Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2)).mul
      (differentiable_xiTail F))
    (fun a b => by
      obtain ⟨C, hC, hb⟩ := exists_halfGaussian_xiTail_le hε a b
      exact ⟨C, hC, hb F⟩)
  simpa only [← dampedTailDatum_eq_halves] using h

/-- The source realizing the damped tail datum. -/
def dampedTailSource (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε)
    (F : Finset XiDivisorSupport) : DeningerMeyerStrongLogTarget :=
  deningerMeyerInverseMellinSource _ (dampedTailDatum_entireRegular g hε F)

theorem mellin_dampedTailSource (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε)
    (F : Finset XiDivisorSupport) :
    deningerMeyerStrongLogMellin (dampedTailSource g hε F) = dampedTailDatum g ε F :=
  funext (deningerMeyerInverseMellinSource_mellin _)

/-! ### 3. Jets of the damped tail source -/

private theorem analyticAt_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (z : ℂ) :
    AnalyticAt ℂ f z :=
  hf.analyticAt z

/-- Outside `F` the tail vanishes to full multiplicity. -/
theorem multiplicity_le_analyticOrderAt_xiTail {F : Finset XiDivisorSupport}
    {σ : XiDivisorSupport} (hσ : σ ∉ F) :
    (xiSupportMultiplicity σ : ℕ∞) ≤ analyticOrderAt (xiTail F) (σ : ℂ) := by
  classical
  have hcomp : analyticOrderAt (xiTail F) (σ : ℂ) = analyticOrderAt
      (canonicalProductE1Tail xiSpectralPoint (supportCopies F)) (spectralCoordinate σ) := by
    have hg : AnalyticAt ℂ spectralCoordinate (σ : ℂ) := by
      unfold spectralCoordinate; fun_prop
    have hd : deriv spectralCoordinate (σ : ℂ) ≠ 0 := by
      have : HasDerivAt spectralCoordinate (-I) (σ : ℂ) := by
        have h := ((hasDerivAt_id (σ : ℂ)).sub_const (1 / 2 : ℂ)).mul_const (-I)
        rw [one_mul] at h
        exact h
      rw [this.deriv]
      exact neg_ne_zero.mpr I_ne_zero
    exact analyticOrderAt_comp_of_deriv_ne_zero hg hd
  rw [hcomp]
  let copies : Finset XiZeroCopy :=
    Finset.univ.map ⟨fun i : Fin (xiSupportMultiplicity σ) => (⟨σ, i⟩ : XiZeroCopy),
      fun i j h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩
  have hcard : copies.card = xiSupportMultiplicity σ := by simp [copies]
  have hw : spectralCoordinate (σ : ℂ) ≠ 0 :=
    xiSpectralPoint_ne_zero ⟨σ, ⟨0, xiSupportMultiplicity_pos σ⟩⟩
  have h := le_analyticOrderAt_canonicalProductE1Tail xiSpectralPoint xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable (supportCopies F) hw copies (fun q hq => by
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp hq
      exact ⟨rfl, fun h => hσ (mem_supportCopies.mp h)⟩)
  rwa [hcard] at h

/-- The datum vanishes wherever both the source and the tail do, to the larger order. -/
theorem le_analyticOrderAt_dampedTailDatum (g : DeningerMeyerStrongLogTarget) (ε : ℝ)
    (F : Finset XiDivisorSupport) (z : ℂ) :
    analyticOrderAt (deningerMeyerStrongLogMellin g) z ≤ analyticOrderAt (dampedTailDatum g ε F) z ∧
      analyticOrderAt (xiTail F) z ≤ analyticOrderAt (dampedTailDatum g ε F) z := by
  have he : AnalyticAt ℂ (fun s : ℂ => Complex.exp ((ε : ℂ) * s ^ 2)) z := by fun_prop
  have hm : AnalyticAt ℂ (deningerMeyerStrongLogMellin g) z :=
    analyticAt_of_differentiable (deningerMeyerStrongLogMellin_entireRegular g).differentiable z
  have ht : AnalyticAt ℂ (xiTail F) z := analyticAt_of_differentiable (differentiable_xiTail F) z
  have hfun : dampedTailDatum g ε F =
      (fun s : ℂ => Complex.exp ((ε : ℂ) * s ^ 2)) * deningerMeyerStrongLogMellin g * xiTail F :=
    rfl
  rw [hfun, analyticOrderAt_mul (he.mul hm) ht, analyticOrderAt_mul he hm]
  exact ⟨le_add_right (le_add_left le_rfl), le_add_left le_rfl⟩

/-- Every jet of the damped tail source vanishes outside `F`, and below `k σ` inside it. -/
theorem jet_dampedTailSource_eq_zero {k : XiDivisorSupport → ℕ}
    {g : DeningerMeyerStrongLogTarget} (hg : g ∈ divisorOrderIdeal k) {ε : ℝ} (hε : 0 < ε)
    (F : Finset XiDivisorSupport) (σ : XiDivisorSupport) (i : DeningerArithmeticJetIndex σ)
    (hσi : σ ∉ F ∨ i.val < k σ) :
    deningerMeyerStrongLogMellinJetLM i.val (σ : ℂ) (dampedTailSource g hε F) = 0 := by
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, mellin_dampedTailSource]
  have hD : AnalyticAt ℂ (dampedTailDatum g ε F) (σ : ℂ) :=
    analyticAt_of_differentiable (dampedTailDatum_entireRegular g hε F).differentiable _
  have horder : ((i.val + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (dampedTailDatum g ε F) (σ : ℂ) := by
    rcases hσi with hσ | hik
    · exact le_trans (by exact_mod_cast i.isLt)
        ((multiplicity_le_analyticOrderAt_xiTail hσ).trans
          (le_analyticOrderAt_dampedTailDatum g ε F σ).2)
    · refine le_trans ?_ (le_analyticOrderAt_dampedTailDatum g ε F σ).1
      have hm : AnalyticAt ℂ (deningerMeyerStrongLogMellin g) (σ : ℂ) :=
        analyticAt_of_differentiable (deningerMeyerStrongLogMellin_entireRegular g).differentiable _
      refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hm).mpr fun j hj => ?_
      have hjm : j < xiSupportMultiplicity σ := lt_of_le_of_lt (Nat.lt_succ_iff.mp hj) i.isLt
      rw [← deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
      exact hg σ ⟨j, hjm⟩ (lt_of_le_of_lt (Nat.lt_succ_iff.mp hj) hik)
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hD).mp horder i.val
    (Nat.lt_succ_self _)

/-! ### 4. Finite repair inside `F` -/

/-- The jet-source repair of a source at the slots of order at least `k ρ` over `F`. -/
def jetRepair (k : XiDivisorSupport → ℕ) (F : Finset XiDivisorSupport)
    (A : DeningerMeyerStrongLogTarget) : DeningerMeyerStrongLogTarget :=
  ∑ ρ ∈ F, ∑ j ∈ (Finset.univ : Finset (DeningerArithmeticJetIndex ρ)).filter
    (fun j => k ρ ≤ j.val),
      deningerMeyerStrongLogMellinJetLM j.val (ρ : ℂ) A • meyerSingleJetSource ρ j

theorem jetRepair_mem (k : XiDivisorSupport → ℕ) (F : Finset XiDivisorSupport)
    (A : DeningerMeyerStrongLogTarget) : jetRepair k F A ∈ orderJetSpan k :=
  Submodule.sum_mem _ fun ρ _ => Submodule.sum_mem _ fun j hj =>
    Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨ρ, j, (Finset.mem_filter.mp hj).2, rfl⟩)

theorem jet_jetRepair (k : XiDivisorSupport → ℕ) (F : Finset XiDivisorSupport)
    (A : DeningerMeyerStrongLogTarget) (σ : XiDivisorSupport)
    (i : DeningerArithmeticJetIndex σ) :
    deningerMeyerStrongLogMellinJetLM i.val (σ : ℂ) (jetRepair k F A) =
      if σ ∈ F ∧ k σ ≤ i.val then deningerMeyerStrongLogMellinJetLM i.val (σ : ℂ) A else 0 := by
  classical
  simp only [jetRepair, map_sum, map_smul, meyerSingleJetSource_jet, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  have hother : ∀ ρ : XiDivisorSupport, ρ ≠ σ →
      (∑ j ∈ (Finset.univ : Finset (DeningerArithmeticJetIndex ρ)).filter (fun j => k ρ ≤ j.val),
        if σ = ρ ∧ i.val = j.val then deningerMeyerStrongLogMellinJetLM j.val (ρ : ℂ) A
        else 0) = 0 :=
    fun ρ hne => Finset.sum_eq_zero fun j _ => if_neg fun h => hne h.1.symm
  by_cases hσ : σ ∈ F
  · rw [Finset.sum_eq_single_of_mem σ hσ fun ρ _ hne => hother ρ hne]
    have hinner : (∑ j ∈ (Finset.univ : Finset (DeningerArithmeticJetIndex σ)).filter
        (fun j => k σ ≤ j.val),
        if σ = σ ∧ i.val = j.val then deningerMeyerStrongLogMellinJetLM j.val (σ : ℂ) A else 0) =
        ∑ j ∈ (Finset.univ : Finset (DeningerArithmeticJetIndex σ)).filter
          (fun j => k σ ≤ j.val),
          if i = j then deningerMeyerStrongLogMellinJetLM j.val (σ : ℂ) A else 0 :=
      Finset.sum_congr rfl fun j _ => by simp only [true_and, Fin.val_inj]
    rw [hinner, Finset.sum_ite_eq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hσ]
  · rw [Finset.sum_eq_zero fun ρ hρ => hother ρ (fun h => hσ (h ▸ hρ)), if_neg fun h => hσ h.1]

/-- The damped tail source lies in `E_k ⊔ R`. -/
theorem dampedTailSource_mem {k : XiDivisorSupport → ℕ} {g : DeningerMeyerStrongLogTarget}
    (hg : g ∈ divisorOrderIdeal k) {ε : ℝ} (hε : 0 < ε) (F : Finset XiDivisorSupport) :
    dampedTailSource g hε F ∈ orderJetSpan k ⊔ poissonBoundary := by
  set A := dampedTailSource g hε F
  have hR : A - jetRepair k F A ∈ poissonBoundary := by
    refine (meyerSource_boundary_iff_jets_zero _).mpr fun σ i => ?_
    rw [map_sub, jet_jetRepair]
    split_ifs with h
    · exact sub_self _
    · rw [sub_zero]
      refine jet_dampedTailSource_eq_zero hg hε F σ i ?_
      by_contra hc
      exact h ⟨not_not.mp (not_or.mp hc).1, not_lt.mp (not_or.mp hc).2⟩
  have hsplit : A = jetRepair k F A + (A - jetRepair k F A) := by abel
  rw [hsplit]
  exact Submodule.add_mem_sup (jetRepair_mem k F A) hR

/-! ### 5. Convergence on vertical Mellin lines -/

/-- Convergence of all vertical Mellin line integrals of the difference gives convergence in the
natural topology. -/
theorem tendsto_of_mellin_line_tendsto {ι : Type*} {l : Filter ι}
    (x : ι → DeningerMeyerStrongLogTarget) (y : DeningerMeyerStrongLogTarget)
    (h : ∀ (n : ℕ) (k : ℤ), Tendsto (fun i => ∫ t : ℝ,
      ‖(-((k : ℂ) + t * I)) ^ n * (deningerMeyerStrongLogMellin (x i) ((k : ℂ) + t * I) -
        deningerMeyerStrongLogMellin y ((k : ℂ) + t * I))‖) l (𝓝 0)) :
    Tendsto x l (𝓝 y) := by
  have herr : Tendsto (fun i => x i - y) l (𝓝 0) := by
    change Tendsto _ _ (@nhds _ (⨅ i : ℕ × ℤ, TopologicalSpace.induced
      (deningerMeyerStrongLogGaugeLinear i.1 i.2) inferInstance) 0)
    rw [nhds_iInf, tendsto_iInf]
    intro p
    rw [nhds_induced, map_zero, tendsto_comap_iff, tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun i => (1 / (2 * Real.pi)) * ∫ t : ℝ,
        ‖(-((p.2 : ℂ) + t * I)) ^ p.1 * (deningerMeyerStrongLogMellin (x i) ((p.2 : ℂ) + t * I) -
          deningerMeyerStrongLogMellin y ((p.2 : ℂ) + t * I))‖) l (𝓝 0) := by
      simpa using (h p.1 p.2).const_mul (1 / (2 * Real.pi))
    refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hlim
    have hb := deningerMeyerStrongLogGauge_le_mellin (x i - y) p.1 p.2
    change ‖deningerMeyerStrongLogGauge p.1 p.2 (x i - y)‖ ≤ _
    refine hb.trans_eq ?_
    congr 1
    apply integral_congr_ae
    filter_upwards with t
    congr 2
    change deningerMeyerStrongLogMellinLM _ (x i - y) = _
    rw [map_sub]
    rfl
  simpa only [sub_add_cancel, zero_add] using herr.add_const y

/-- The damped source without tail, i.e. the Gaussian regularization of `g`. -/
def dampedSource (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    DeningerMeyerStrongLogTarget :=
  deningerMeyerInverseMellinSource _ (deningerMeyerStrongLogMellin_gaussianRegular g hε)

/-- **Exhaustion by tails.** As `F` exhausts the Xi divisor, the damped tail sources converge to
the damped source in the natural topology. -/
theorem tendsto_dampedTailSource (g : DeningerMeyerStrongLogTarget) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun F : Finset XiDivisorSupport => dampedTailSource g hε F) atTop
      (𝓝 (dampedSource g hε)) := by
  refine tendsto_of_mellin_line_tendsto _ _ fun n k => ?_
  set P : ℂ → ℂ := fun s => (-s) ^ n *
    deningerGaussianMellinRegularization (ε / 2) (deningerMeyerStrongLogMellin g) s
  have hP := (deningerMeyerStrongLogMellin_gaussianRegular g (half_pos hε)).signedPow n
  have hPint := (hP ((k : ℝ) - 1) ((k : ℝ) + 1)).integrable_line
    (c := (k : ℝ)) (by linarith) (by linarith)
  obtain ⟨C, hC, hCb⟩ := exists_halfGaussian_xiTail_le hε (k : ℝ) (k : ℝ)
  set B : ℝ := C + Real.exp (ε / 2 * (k : ℝ) ^ 2)
  have hmellin (F : Finset XiDivisorSupport) (s : ℂ) :
      (-s) ^ n * (deningerMeyerStrongLogMellin (dampedTailSource g hε F) s -
        deningerMeyerStrongLogMellin (dampedSource g hε) s) =
        P s * (Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2) * (xiTail F s - 1)) := by
    rw [mellin_dampedTailSource, dampedSource, deningerMeyerInverseMellinSource_mellin,
      dampedTailDatum_eq_halves]
    simp only [P, deningerGaussianMellinRegularization]
    have he : Complex.exp ((ε : ℂ) * s ^ 2) =
        Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2) * Complex.exp (((ε / 2 : ℝ) : ℂ) * s ^ 2) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    ring
  have hline_re (t : ℝ) : (((k : ℝ) : ℂ) + t * I).re = (k : ℝ) := by simp
  have hfac (F : Finset XiDivisorSupport) (t : ℝ) :
      ‖Complex.exp (((ε / 2 : ℝ) : ℂ) * (((k : ℝ) : ℂ) + t * I) ^ 2) *
        (xiTail F (((k : ℝ) : ℂ) + t * I) - 1)‖ ≤ B := by
    rw [mul_sub, mul_one]
    refine (norm_sub_le _ _).trans (add_le_add (hCb F _ (hline_re t).ge (hline_re t).le) ?_)
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [pow_two, Complex.mul_re, Complex.mul_im, add_re, add_im, ofReal_re, ofReal_im,
      mul_re, mul_im, I_re, I_im]
    nlinarith [sq_nonneg t, hε.le]
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := (atTop : Filter (Finset XiDivisorSupport)))
    (fun t : ℝ => ‖P (((k : ℝ) : ℂ) + t * I)‖ * B) (f := fun _ => (0 : ℝ))
    (F := fun (F : Finset XiDivisorSupport) (t : ℝ) =>
      ‖P (((k : ℝ) : ℂ) + t * I) * (Complex.exp (((ε / 2 : ℝ) : ℂ) *
        (((k : ℝ) : ℂ) + t * I) ^ 2) * (xiTail F (((k : ℝ) : ℂ) + t * I) - 1))‖)
    (Eventually.of_forall fun F => (show Continuous (fun t : ℝ =>
      ‖P (((k : ℝ) : ℂ) + t * I) * (Complex.exp (((ε / 2 : ℝ) : ℂ) *
        (((k : ℝ) : ℂ) + t * I) ^ 2) * (xiTail F (((k : ℝ) : ℂ) + t * I) - 1))‖) from
      (((hP.differentiable.continuous.comp (by fun_prop)).mul
        ((by fun_prop : Continuous fun t : ℝ =>
          Complex.exp (((ε / 2 : ℝ) : ℂ) * (((k : ℝ) : ℂ) + t * I) ^ 2)).mul
          (((differentiable_xiTail F).continuous.comp (by fun_prop)).sub
            continuous_const))).norm)).aestronglyMeasurable)
    (Eventually.of_forall fun F => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_norm, norm_mul]
      exact mul_le_mul_of_nonneg_left (hfac F t) (norm_nonneg _))
    (hPint.norm.mul_const B)
    (Eventually.of_forall fun t => by
      have hlim := ((tendsto_xiTail_one (((k : ℝ) : ℂ) + t * I)).sub_const 1).const_mul
        (P (((k : ℝ) : ℂ) + t * I) * Complex.exp (((ε / 2 : ℝ) : ℂ) *
          (((k : ℝ) : ℂ) + t * I) ^ 2))
      simpa [mul_assoc] using hlim.norm)
  simp only [integral_zero] at hd
  refine hd.congr' (Eventually.of_forall fun F => ?_)
  apply integral_congr_ae
  filter_upwards with t
  rw [hmellin]
  push_cast
  rfl

/-! ### 6. Spectral synthesis -/

/-- **Spectral synthesis for divisor-order ideals.** In the natural Fréchet topology,
`closure (E_k ⊔ R) = I_k`: every source vanishing to order `k ρ` at each Xi zero is a limit of
finite combinations of the jet sources of order `≥ k ρ` plus Poisson boundaries. -/
theorem closure_orderJetSpan_sup_poissonBoundary (k : XiDivisorSupport → ℕ) :
    closure ((orderJetSpan k ⊔ poissonBoundary : Submodule ℂ DeningerMeyerStrongLogTarget) :
      Set DeningerMeyerStrongLogTarget) = divisorOrderIdeal k := by
  apply subset_antisymm
  · exact closure_minimal (orderJetSpan_sup_poissonBoundary_le k) (isClosed_divisorOrderIdeal k)
  · intro g hg
    have hε (m : ℕ) : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hdamped (m : ℕ) : dampedSource g (hε m) ∈ closure
        ((orderJetSpan k ⊔ poissonBoundary : Submodule ℂ DeningerMeyerStrongLogTarget) :
          Set DeningerMeyerStrongLogTarget) :=
      mem_closure_of_tendsto (tendsto_dampedTailSource g (hε m))
        (Eventually.of_forall fun F => dampedTailSource_mem hg (hε m) F)
    exact isClosed_closure.mem_of_tendsto (deningerMeyerGaussianSource_tendsto g)
      (Eventually.of_forall hdamped)

/-! ### 7. The blind ideals -/

/-- Vanishing order equal to the multiplicity off the line, none on it. -/
def offLineFullOrder (ρ : XiDivisorSupport) : ℕ :=
  open Classical in if (ρ : ℂ).re = 1 / 2 then 0 else xiSupportMultiplicity ρ

/-- Vanishing order one off the line, none on it. -/
def offLineValueOrder (ρ : XiDivisorSupport) : ℕ :=
  open Classical in if (ρ : ℂ).re = 1 / 2 then 0 else 1

/-- The span of the critical jet sources. -/
def criticalJetSpan : Submodule ℂ DeningerMeyerStrongLogTarget :=
  Submodule.span ℂ {g | ∃ (ρ : XiDivisorSupport) (j : DeningerArithmeticJetIndex ρ),
    (ρ : ℂ).re = 1 / 2 ∧ g = meyerSingleJetSource ρ j}

/-- The full-jet blind ideal: every off-line jet vanishes. -/
def fullJetBlindIdeal : Set DeningerMeyerStrongLogTarget :=
  {g | ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≠ 1 / 2 → ∀ j : DeningerArithmeticJetIndex ρ,
    deningerMeyerStrongLogMellinJetLM j.val (ρ : ℂ) g = 0}

theorem orderJetSpan_offLineFullOrder : orderJetSpan offLineFullOrder = criticalJetSpan := by
  unfold orderJetSpan criticalJetSpan offLineFullOrder
  congr 1
  ext g
  constructor
  · rintro ⟨ρ, j, hkj, rfl⟩
    refine ⟨ρ, j, ?_, rfl⟩
    by_contra h
    rw [if_neg h] at hkj
    exact absurd j.isLt (not_lt.mpr hkj)
  · rintro ⟨ρ, j, hρ, rfl⟩
    exact ⟨ρ, j, by rw [if_pos hρ]; exact Nat.zero_le _, rfl⟩

theorem divisorOrderIdeal_offLineFullOrder :
    (divisorOrderIdeal offLineFullOrder : Set DeningerMeyerStrongLogTarget) = fullJetBlindIdeal := by
  ext g
  simp only [SetLike.mem_coe, fullJetBlindIdeal, Set.mem_setOf_eq]
  constructor
  · intro hg ρ hρ j
    exact hg ρ j (by unfold offLineFullOrder; rw [if_neg hρ]; exact j.isLt)
  · intro hg ρ j hj
    have hρ : (ρ : ℂ).re ≠ 1 / 2 := fun h => by
      unfold offLineFullOrder at hj; rw [if_pos h] at hj; exact Nat.not_lt_zero _ hj
    exact hg ρ hρ j

/-- **The critical jet sources synthesize the full-jet blind ideal.** -/
theorem closure_criticalJetSpan_sup_poissonBoundary :
    closure ((criticalJetSpan ⊔ poissonBoundary : Submodule ℂ DeningerMeyerStrongLogTarget) :
      Set DeningerMeyerStrongLogTarget) = fullJetBlindIdeal := by
  rw [← orderJetSpan_offLineFullOrder, closure_orderJetSpan_sup_poissonBoundary,
    divisorOrderIdeal_offLineFullOrder]

/-- The zeroth jet is the Mellin value. -/
theorem jet_zero_eq_mellin (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellinJetLM 0 s g = deningerMeyerStrongLogMellin g s := by
  rw [deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv, iteratedDeriv_zero]

theorem divisorOrderIdeal_offLineValueOrder :
    (divisorOrderIdeal offLineValueOrder : Set DeningerMeyerStrongLogTarget) =
      meyerTraceBoundedIdeal := by
  ext g
  change _ ↔ MeyerTraceOrbitBounded g
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
  simp only [SetLike.mem_coe]
  constructor
  · intro hg ρ hρ
    rw [← jet_zero_eq_mellin]
    exact hg ρ ⟨0, xiSupportMultiplicity_pos ρ⟩
      (by unfold offLineValueOrder; rw [if_neg hρ]; exact Nat.one_pos)
  · intro hg ρ j hj
    have hρ : (ρ : ℂ).re ≠ 1 / 2 := fun h => by
      unfold offLineValueOrder at hj; rw [if_pos h] at hj; exact Nat.not_lt_zero _ hj
    have hj0 : j.val = 0 := by
      unfold offLineValueOrder at hj; rw [if_neg hρ] at hj; omega
    rw [hj0, jet_zero_eq_mellin]
    exact hg ρ hρ

/-- The jet sources lying in the value-blind ideal: all critical jets and the off-line jets of
positive order. -/
def valueBlindJetSpan : Submodule ℂ DeningerMeyerStrongLogTarget :=
  Submodule.span ℂ {g | ∃ (ρ : XiDivisorSupport) (j : DeningerArithmeticJetIndex ρ),
    ((ρ : ℂ).re = 1 / 2 ∨ 1 ≤ j.val) ∧ g = meyerSingleJetSource ρ j}

theorem orderJetSpan_offLineValueOrder : orderJetSpan offLineValueOrder = valueBlindJetSpan := by
  unfold orderJetSpan valueBlindJetSpan offLineValueOrder
  congr 1
  ext g
  constructor
  · rintro ⟨ρ, j, hkj, rfl⟩
    refine ⟨ρ, j, ?_, rfl⟩
    by_cases h : (ρ : ℂ).re = 1 / 2
    · exact Or.inl h
    · rw [if_neg h] at hkj; exact Or.inr hkj
  · rintro ⟨ρ, j, hρ, rfl⟩
    refine ⟨ρ, j, ?_, rfl⟩
    by_cases h : (ρ : ℂ).re = 1 / 2
    · rw [if_pos h]; exact Nat.zero_le _
    · rw [if_neg h]; exact hρ.resolve_left h

/-- **Spectral synthesis of the blind ideal.** `meyerTraceBoundedIdeal` is the closure of its own
jet sources (every critical jet, the off-line jets of positive order) and the Poisson boundary. -/
theorem closure_valueBlindJetSpan_sup_poissonBoundary :
    closure ((valueBlindJetSpan ⊔ poissonBoundary : Submodule ℂ DeningerMeyerStrongLogTarget) :
      Set DeningerMeyerStrongLogTarget) = meyerTraceBoundedIdeal := by
  rw [← orderJetSpan_offLineValueOrder, closure_orderJetSpan_sup_poissonBoundary,
    divisorOrderIdeal_offLineValueOrder]

/-- **Critical jets suffice exactly when the off-line zeros are simple.** -/
theorem closure_criticalJetSpan_sup_eq_meyerTraceBoundedIdeal_iff :
    closure ((criticalJetSpan ⊔ poissonBoundary : Submodule ℂ DeningerMeyerStrongLogTarget) :
      Set DeningerMeyerStrongLogTarget) = meyerTraceBoundedIdeal ↔
      ∀ ρ : XiDivisorSupport, (ρ : ℂ).re ≠ 1 / 2 → xiSupportMultiplicity ρ = 1 := by
  rw [closure_criticalJetSpan_sup_poissonBoundary]
  constructor
  · intro heq ρ hρ
    by_contra hm
    have h2 : 1 < xiSupportMultiplicity ρ := by
      have := xiSupportMultiplicity_pos ρ; omega
    let j : DeningerArithmeticJetIndex ρ := ⟨1, h2⟩
    have hmem : meyerSingleJetSource ρ j ∈ (meyerTraceBoundedIdeal :
        Set DeningerMeyerStrongLogTarget) := by
      change MeyerTraceOrbitBounded _
      rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
      intro σ _
      rw [← jet_zero_eq_mellin]
      have h := meyerSingleJetSource_jet ρ j σ ⟨0, xiSupportMultiplicity_pos σ⟩
      rw [h, if_neg]
      rintro ⟨-, h01⟩
      exact absurd h01 (by simp [j])
    rw [← heq] at hmem
    have h := hmem ρ hρ j
    rw [meyerSingleJetSource_jet, if_pos ⟨rfl, rfl⟩] at h
    exact one_ne_zero h
  · intro hsimple
    rw [← divisorOrderIdeal_offLineFullOrder, ← divisorOrderIdeal_offLineValueOrder]
    congr 2
    funext ρ
    unfold offLineFullOrder offLineValueOrder
    split_ifs with h
    · rfl
    · exact hsimple ρ h

/-- **Exhaustion as a density statement.** RH holds iff the critical jet sources and the Poisson
boundary are dense in the whole Meyer source. -/
theorem closure_criticalJetSpan_sup_poissonBoundary_eq_univ_iff :
    closure ((criticalJetSpan ⊔ poissonBoundary : Submodule ℂ DeningerMeyerStrongLogTarget) :
      Set DeningerMeyerStrongLogTarget) = Set.univ ↔ RiemannHypothesis := by
  rw [closure_criticalJetSpan_sup_poissonBoundary]
  constructor
  · intro huniv
    rw [← meyerTraceBoundedIdeal_eq_top_iff]
    refine Submodule.eq_top_iff'.mpr fun g => ?_
    change MeyerTraceOrbitBounded g
    rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
    intro ρ hρ
    have hg : g ∈ fullJetBlindIdeal := huniv ▸ Set.mem_univ g
    rw [← jet_zero_eq_mellin]
    exact hg ρ hρ ⟨0, xiSupportMultiplicity_pos ρ⟩
  · intro hRH
    exact Set.eq_univ_of_forall fun g ρ hρ =>
      absurd (xi_divisor_support_re_eq_half_of_rh hRH ρ) hρ

end GaloisForLFunctions.ArithmeticPositiveDuality
