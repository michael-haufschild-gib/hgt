import GaloisForLFunctions.RHTower.SarnakXueInner
import GaloisForLFunctions.RHTower.SarnakXueUnfolding
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

open MeasureTheory UpperHalfPlane ModularGroup Set
open scoped MatrixGroups Pointwise ENNReal

/-!
# The pretrace inequality for principal congruence eigenspaces

`Γ̄(p)`, the image of `Γ(p)` in `PSL(2,ℤ)`, has the fundamental domain `⋃_c R_c · 𝒟` built from right
coset representatives (`isFundamentalDomain_cellP`). Its `L²` mass is bounded by the coset-sum inner
product (`lintegral_cellP_le`), and the unfolded Cauchy–Schwarz inequality gives, for every eigenspace
vector `u`, centre `w` and radius `R`,
`(∫_{B_R(w)} |u|)² ≤ (Σ_{h ∈ Γ̄(p)} μ(B_R(w) ∩ h B_R(w))) ⟨u, u⟩` (`pretrace`).
-/

namespace GaloisForLFunctions.RHTower.SarnakXuePretrace

open GaloisForLFunctions.HTGeometry
open CongruenceSubgroup

noncomputable section

variable (p : ℕ)

/-- The image of `Γ(p)` in `PSL(2,ℤ)`. -/
def gammaBar : Subgroup PSL2Z := (Gamma p).map (QuotientGroup.mk' modularActionKernel)

instance : MeasurableConstSMul (gammaBar p) ℍ :=
  ⟨fun h => measurable_const_smul (h : PSL2Z)⟩

instance : SMulInvariantMeasure (gammaBar p) ℍ volume :=
  ⟨fun h _ hs => SMulInvariantMeasure.measure_preimage_smul (h : PSL2Z) hs⟩

/-- Right cosets of `Γ̄(p)` in `PSL(2,ℤ)`. -/
abbrev Cosets := Quotient (QuotientGroup.rightRel (gammaBar p))

/-- The union of the translates of the modular cell by coset representatives. -/
def cellP : Set ℍ := ⋃ c : Cosets p, (Quotient.out c : PSL2Z) • fd

theorem isFundamentalDomain_cellP : IsFundamentalDomain (gammaBar p) (cellP p) volume := by
  apply isFundamentalDomain_iUnion_smul_of_cosetReps isFundamentalDomain_fd (gammaBar p)
    (fun c : Cosets p => Quotient.out c)
  · intro g
    set c : Cosets p := Quotient.mk _ g
    have hc : QuotientGroup.rightRel (gammaBar p) (Quotient.out c) g := Quotient.mk_out (s := _) g
    have hmem : g * (Quotient.out c)⁻¹ ∈ gammaBar p := QuotientGroup.rightRel_apply.mp hc
    exact ⟨⟨_, hmem⟩, c, by simp⟩
  · intro h h' c c' heq
    have hcc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      apply Quotient.sound
      show QuotientGroup.rightRel (gammaBar p) _ _
      rw [QuotientGroup.rightRel_apply]
      have : Quotient.out c' * (Quotient.out c)⁻¹ = (h' : PSL2Z)⁻¹ * h := by
        calc Quotient.out c' * (Quotient.out c)⁻¹
            = (h' : PSL2Z)⁻¹ * ((h' : PSL2Z) * Quotient.out c') * (Quotient.out c)⁻¹ := by group
          _ = (h' : PSL2Z)⁻¹ * ((h : PSL2Z) * Quotient.out c) * (Quotient.out c)⁻¹ := by rw [heq]
          _ = _ := by group
      rw [this]
      exact mul_mem (inv_mem h'.2) h.2
    subst hcc
    refine ⟨Subtype.ext (mul_right_cancel heq), rfl⟩


theorem lintegral_smul_set (g : PSL2Z) (s : Set ℍ) (F : ℍ → ℝ≥0∞) :
    ∫⁻ x in g • s, F x = ∫⁻ x in s, F (g • x) := by
  rw [(measurePreserving_smul g volume).setLIntegral_comp_emb (measurableEmbedding_const_smul g),
    Set.image_smul]

open GaloisForLFunctions.RHTower
open GaloisForLFunctions.RHTower.SarnakXueInner
open GaloisForLFunctions.RHTower.SelbergMaassCongruenceTrace
open GaloisForLFunctions.RHTower.MaassCongruenceL2

variable {N : ℕ} {lam : ℝ}

theorem V_inv (u : V N lam) {A : SL(2, ℤ)} (hA : A ∈ Gamma (N + 1)) (z : ℍ) : u.1 (A • z) = u.1 z :=
  SarnakXue.sl_inv N lam u.2 A hA z

theorem V_inv_conj (u : V N lam) (B : SL(2, ℤ)) {A : SL(2, ℤ)} (hA : A ∈ Gamma (N + 1)) (z : ℍ) :
    u.1 ((B * A) • z) = u.1 (B • z) := by
  have hc : B * A * B⁻¹ ∈ Gamma (N + 1) := (Gamma_normal (N + 1)).conj_mem A hA B
  have := V_inv u hc (B • z)
  rwa [mul_smul, mul_smul, inv_smul_smul, ← mul_smul] at this

theorem gammaBar_smul (h : gammaBar (N + 1)) (u : V N lam) (x : ℍ) : u.1 (h • x) = u.1 x := by
  obtain ⟨γ, hγ, he⟩ := h.2
  have : h • x = γ • x := by
    rw [Subgroup.smul_def, ← he]
    exact PSL2Z_mk_smul γ x
  rw [this, V_inv u hγ]

/-- Each coset representative is represented by a class in `Deck`. -/
def cosetDeck (c : Cosets (N + 1)) : Deck N :=
  QuotientGroup.mk (Quotient.out (Quotient.out c : PSL2Z) : SL(2, ℤ))

theorem cosetDeck_injective : Function.Injective (cosetDeck (N := N)) := by
  intro c c' h
  set A := Quotient.out (Quotient.out c : PSL2Z)
  set A' := Quotient.out (Quotient.out c' : PSL2Z)
  have hAA : A⁻¹ * A' ∈ Gamma (N + 1) := QuotientGroup.eq.mp h
  have hmem : A' * A⁻¹ ∈ Gamma (N + 1) := by
    have := (Gamma_normal (N + 1)).conj_mem _ hAA A
    simpa [mul_assoc] using this
  rw [← Quotient.out_eq c, ← Quotient.out_eq c']
  apply Quotient.sound
  show QuotientGroup.rightRel (gammaBar (N + 1)) _ _
  rw [QuotientGroup.rightRel_apply]
  have e1 : (Quotient.out c : PSL2Z) = QuotientGroup.mk A := (Quotient.out_eq _).symm
  have e2 : (Quotient.out c' : PSL2Z) = QuotientGroup.mk A' := (Quotient.out_eq _).symm
  rw [e1, e2, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  exact ⟨_, hmem, rfl⟩

theorem cosetDeck_eval (u : V N lam) (c : Cosets (N + 1)) (z : ℍ) :
    u.1 ((Quotient.out c : PSL2Z) • z) = u.1 ((cosetDeck c).out • z) := by
  set A := Quotient.out (Quotient.out c : PSL2Z)
  have e1 : (Quotient.out c : PSL2Z) = QuotientGroup.mk A := (Quotient.out_eq _).symm
  rw [e1, PSL2Z_mk_smul]
  have hq : A⁻¹ * (cosetDeck c).out ∈ Gamma (N + 1) := by
    have := QuotientGroup.out_eq' (cosetDeck c)
    exact QuotientGroup.eq.mp (this.trans rfl).symm
  have := V_inv_conj u A hq z
  rw [mul_inv_cancel_left] at this
  exact this.symm

/-- The fundamental domain of `Γ̄(p)` carries at most the coset-sum mass. -/
theorem lintegral_cellP_le (u : V N lam) :
    ∫⁻ x in cellP (N + 1), ‖u.1 x‖ₑ ^ 2 ≤ ENNReal.ofReal (ip u u).re := by
  calc ∫⁻ x in cellP (N + 1), ‖u.1 x‖ₑ ^ 2
      ≤ ∑' c : Cosets (N + 1), ∫⁻ x in (Quotient.out c : PSL2Z) • fd, ‖u.1 x‖ₑ ^ 2 :=
        lintegral_iUnion_le _ _
    _ = ∑' c : Cosets (N + 1), ∫⁻ x in fd, ‖u.1 ((cosetDeck c).out • x)‖ₑ ^ 2 := by
        apply tsum_congr; intro c
        rw [lintegral_smul_set]
        simp_rw [cosetDeck_eval]
    _ ≤ ∑' q : Deck N, ∫⁻ x in fd, ‖u.1 (q.out • x)‖ₑ ^ 2 :=
        ENNReal.tsum_comp_le_tsum_of_injective cosetDeck_injective
          (fun q => ∫⁻ x in fd, ‖u.1 (q.out • x)‖ₑ ^ 2)
    _ = ∫⁻ x in fd, ∑ q : Deck N, ‖u.1 (q.out • x)‖ₑ ^ 2 := by
        rw [tsum_fintype, lintegral_finsetSum]
        intro q _
        exact (((V_continuous u).comp (continuous_sl_smul _)).measurable.enorm).pow_const 2
    _ = ENNReal.ofReal (ip u u).re := by
        rw [ip_self, Complex.ofReal_re, ofReal_integral_eq_lintegral_ofReal]
        · apply lintegral_congr
          intro x
          rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => Complex.normSq_nonneg _)]
          apply Finset.sum_congr rfl
          intro q _
          rw [Complex.normSq_eq_norm_sq, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
        · have h2 := ((ipDensity_integrable u u).congr
            (Filter.Eventually.of_forall (fun z => ipDensity_self u z))).re
          simpa using h2
        · exact Filter.Eventually.of_forall (fun x =>
            Finset.sum_nonneg (fun q _ => Complex.normSq_nonneg _))


open GaloisForLFunctions.RHTower.SarnakXueUnfolding in
/-- **Pretrace inequality.** For every eigenspace vector `u`, centre `w` and radius `R`,
`(∫_{B_R(w)} |u|)² ≤ (Σ_{h ∈ Γ̄(p)} μ(B_R(w) ∩ h B_R(w))) · ⟨u, u⟩`. -/
theorem pretrace (u : V N lam) (w : ℍ) (R : ℝ) :
    (∫⁻ z in Metric.closedBall w R, ‖u.1 z‖ₑ) ^ 2 ≤
      (∑' h : gammaBar (N + 1), volume (Metric.closedBall w R ∩ h • Metric.closedBall w R)) *
        ENNReal.ofReal (ip u u).re := by
  have hm : Measurable (fun z => ‖u.1 z‖ₑ) := (V_continuous u).measurable.enorm
  refine (lintegral_set_sq_le (isFundamentalDomain_cellP (N + 1)) Metric.isClosed_closedBall.measurableSet
    hm (fun h x => by simp only [gammaBar_smul h u x])).trans ?_
  exact mul_le_mul_right (lintegral_cellP_le u) _

end
end GaloisForLFunctions.RHTower.SarnakXuePretrace
