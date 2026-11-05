import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary
import GaloisForLFunctions.WindowVisibilityLaw.CoherentClusterAndTiltAmplificationLaw
import GaloisForLFunctions.WindowVisibilityLaw.ShallowClusterExclusionAndTaperedCrystalBarrier
import GaloisForLFunctions.WindowVisibilityLaw.SplitColumnThresholdAndPerturbedFragility

/-!
# Complete Synthesis of the Window Visibility Law

This module synthesizes the complete answer to the window visibility problem — determining which
off-line zeros a window of half-width `a` can see — across arbitrary tempered zero configurations
and for `zetaZeroConfig`:

1. **Exact closed-interval law (`window_visibility_closed_interval_law`,
   `zeta_and_ahd_onset_dictionary`).** Every tempered configuration `Z` has a right-closed
   positivity interval `[0, onsetAperture Z]` on which seeing `(V1)` and hiding `(V2)` are exact
   contrapositives (`WindowPositiveAt Z a ↔ (a : EReal) ≤ onsetAperture Z`), with
   `onsetAperture Z = ⊤ ↔ ∀ ρ ∈ Z.carrier, ρ.re = 1/2`. For `ζ`, `RH ↔ onsetAperture = ⊤`, off RH
   `onsetAperture = zetaContactAperture` (achieved at the contact endpoint), and
   `AHD.windowThreshold A = ⊤ ↔ ((A/2 : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig`.
2. **Exact two-regime coherent cluster brackets
   (`onsetAperture_multiplicityPairConfig_mem_deep_interval`,
   `onsetAperture_multiplicityPairConfig_mem_cubic_interval`).** A multiplicity-`k` off-line cluster
   in a `2π/L` RvM background satisfies `WindowPositiveAt Z a ↔ k · pairEnergy δ a ≤ L`, yielding
   two-sided `EReal` brackets for `onsetAperture Z` in both the deep logarithmic regime
   `a* ≍ (1/(2δ)) log(4δL/k)` and the shallow cubic regime `a* ≍ (3L/(2kδ²))^{1/3}`.
3. **Exact `Π29` ridge equality (`onsetAperture_perturbedOffLineLatticeConfig_eq`) and the four
   structural dichotomies (`shallow_coherence_vs_nonlattice_hiding_dichotomy`,
   `aperture_height_duality_shielded_vs_unshielded`,
   `split_column_and_perturbed_lattice_dichotomy`,
   `zeta_programme_consequences_of_window_visibility`).** Perturbed off-line columns retain exact
   onset aperture `L/2` on the exponentially thin `ℓ¹` ridge `2 L e^{δL} ∑_k |ε_k| ≤ 1`, whereas a
   single `ε`-defect collapses `onsetAperture` to `(1/(2δ)) log(δL/ε²)`; mixed column families obey
   the sharp split-density threshold `π D_on + (π/2) D_off` (`(g − ½) log q` for `2g` curve
   columns); `DCI`-admissible shallow coherent clusters break naive `(V2)` down to `δ ≳ a^{−3/2}`
   while general non-lattice sets hide whenever unit-window depth-squared mass satisfies
   `W ≲ L / a³`; and smooth biquadratic crystal packets shield depth-`1/a` zeros above single
   exponential height `L ≥ 4a` while unshielded clusters are excluded to doubly-exponential height.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### 1. Master closed-interval law `(V1)` / `(V2)` and the `ζ` / `AHD` dictionary -/

/-- **Master closed-interval window visibility law (`(V1)` seeing & `(V2)` hiding).**
For every tempered zero configuration `Z`:
1. `WindowPositiveAt Z a ↔ (a : EReal) ≤ onsetAperture Z` for all `a ≥ 0`;
2. `∃ f ∈ C²_c([−a, a]), Re W_Z(f, f) < 0` iff `onsetAperture Z < (a : EReal)` for all `a ≥ 0`;
3. `hodgeDefectAt Z a = 0 ↔ (a : EReal) ≤ onsetAperture Z` for all `a ≥ 0`;
4. `onsetAperture Z = ⊤` iff every zero of `Z` lies on the critical line `Re ρ = 1/2`. -/
theorem window_visibility_closed_interval_law {Z : ZeroConfig} (hZ : TemperedConfig Z) :
    (∀ {a : ℝ}, 0 ≤ a → (WindowPositiveAt Z a ↔ (a : EReal) ≤ onsetAperture Z)) ∧
      (∀ {a : ℝ}, 0 ≤ a →
        ((∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ (Z.W f f).re < 0) ↔
          onsetAperture Z < (a : EReal))) ∧
      (∀ {a : ℝ}, 0 ≤ a → (hodgeDefectAt Z a = 0 ↔ (a : EReal) ≤ onsetAperture Z)) ∧
      (onsetAperture Z = ⊤ ↔ ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) :=
  ⟨fun ha => windowPositiveAt_iff_le_onsetAperture hZ ha,
    fun ha => exists_re_W_neg_iff_onsetAperture_lt hZ ha,
    fun ha => hodgeDefectAt_eq_zero_iff_le_onsetAperture hZ ha,
    onsetAperture_eq_top_iff_onLine hZ⟩

/-- **Complete `ζ`, `P1`, and `AHD` onset-aperture dictionary.**
1. Complex and real window positivity coincide on `zetaZeroConfig` at every half-width `a`;
2. `RiemannHypothesis ↔ onsetAperture zetaZeroConfig = ⊤`;
3. Off RH, `onsetAperture zetaZeroConfig = zetaContactAperture` and `ZetaWindowPositive` holds at
   `zetaContactAperture` itself;
4. Unconditionally, `enlargedWeilFloorAperture ≤ onsetAperture zetaZeroConfig`;
5. For every window length `A ≥ 0`, `AHD.windowThreshold A = ⊤` iff
   `((A / 2 : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig`. -/
theorem zeta_and_ahd_onset_dictionary :
    (∀ a : ℝ, WindowPositiveAt zetaZeroConfig a ↔ ZetaWindowPositive a) ∧
      (RiemannHypothesis ↔ onsetAperture zetaZeroConfig = ⊤) ∧
      (¬ RiemannHypothesis →
        onsetAperture zetaZeroConfig = (zetaContactAperture : EReal) ∧
          ZetaWindowPositive zetaContactAperture) ∧
      (((enlargedWeilFloorAperture : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig) ∧
      (∀ {A : ℝ}, 0 ≤ A →
        (windowThreshold A = ⊤ ↔ ((A / 2 : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig)) :=
  ⟨windowPositiveAt_zeta_iff,
    riemannHypothesis_iff_onsetAperture_zeta_eq_top,
    fun hRH => ⟨onsetAperture_zeta_eq_contact_of_not_rh hRH,
      zetaWindowPositive_contact_of_not_rh hRH⟩,
    enlargedWeilFloorAperture_le_onsetAperture_zeta,
    fun hA => windowThreshold_eq_top_iff_le_onsetAperture hA⟩

/-! ### 2. Two-sided `EReal` brackets for coherent cluster onset apertures -/

/-- **Two-sided deep logarithmic bracket for `onsetAperture (multiplicityPairConfig …)`.**
Whenever `0 < a₁, a₂ ≤ L/2` satisfy `2δa₁ ≤ log(4δL/k)` and `log(4δ(L/k + a₂) + 2) ≤ 2δa₂`, the
onset aperture lies in `[a₁, a₂)`:
`(a₁ : EReal) ≤ onsetAperture Z < (a₂ : EReal)`. -/
theorem onsetAperture_multiplicityPairConfig_mem_deep_interval (k : ℕ) (hk : 1 ≤ k)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₁L : a₁ ≤ L / 2) (ha₂ : 0 < a₂) (ha₂L : a₂ ≤ L / 2)
    (hlow : 2 * δ * a₁ ≤ Real.log (4 * δ * L / k))
    (hhigh : Real.log (4 * δ * (L / k + a₂) + 2) ≤ 2 * δ * a₂) :
    (a₁ : EReal) ≤ onsetAperture (multiplicityPairConfig k hk hL hδ hδ' γ₀) ∧
      onsetAperture (multiplicityPairConfig k hk hL hδ hδ' γ₀) < (a₂ : EReal) :=
  ⟨le_onsetAperture_of_windowPositiveAt ha₁.le
      (windowPositiveAt_multiplicityPairConfig_of_le_log k hk hL hδ hδ' γ₀ ha₁ ha₁L hlow),
    onsetAperture_multiplicityPairConfig_lt_of_log_le k hk hL hδ hδ' γ₀ ha₂ ha₂L hhigh⟩

/-- **Two-sided shallow cubic bracket for `onsetAperture (multiplicityPairConfig …)`.**
Whenever `0 < a₁, a₂ ≤ L/2` satisfy `(2/3) k δ² a₁³ cosh(2δa₁) ≤ L` and `L < (2/3) k δ² a₂³`, the
onset aperture lies in `[a₁, a₂)`:
`(a₁ : EReal) ≤ onsetAperture Z < (a₂ : EReal)`. -/
theorem onsetAperture_multiplicityPairConfig_mem_cubic_interval (k : ℕ) (hk : 1 ≤ k)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₁L : a₁ ≤ L / 2) (ha₂ : 0 < a₂) (ha₂L : a₂ ≤ L / 2)
    (hlow : 2 / 3 * (k : ℝ) * δ ^ 2 * a₁ ^ 3 * Real.cosh (2 * δ * a₁) ≤ L)
    (hhigh : L < 2 / 3 * (k : ℝ) * δ ^ 2 * a₂ ^ 3) :
    (a₁ : EReal) ≤ onsetAperture (multiplicityPairConfig k hk hL hδ hδ' γ₀) ∧
      onsetAperture (multiplicityPairConfig k hk hL hδ hδ' γ₀) < (a₂ : EReal) :=
  ⟨le_onsetAperture_of_windowPositiveAt ha₁.le
      (windowPositiveAt_multiplicityPairConfig_of_cubic_le k hk hL hδ hδ' γ₀ ha₁ ha₁L hlow),
    onsetAperture_multiplicityPairConfig_lt_of_lt_cubic k hk hL hδ hδ' γ₀ ha₂ ha₂L hhigh⟩

/-! ### 3. Exact `L/2` onset equality on the `Π29` exponentially thin `ℓ¹` ridge -/

/-- **Exact onset aperture `L/2` of perturbed off-line columns on the `e^{−δL}` `ℓ¹` ridge (`Π29`).**
If `|ε_k| ≤ π/(2L)`, `Summable (fun k => |ε_k|)`, and `2 * L * exp(δ * L) * (∑' k, |ε_k|) ≤ 1`,
then `perturbedOffLineLatticeConfig` has exact onset aperture `L/2`:
* `((L/2 : ℝ) : EReal) ≤ onsetAperture` by `windowPositiveAt_perturbedOffLineLatticeConfig` at
  `a = L/2`;
* `onsetAperture ≤ ((L/2 : ℝ) : EReal)` by `onsetAperture_le_half_pi_density_of_all_offLine_columns`
  since all zeros lie on a single pair of perturbed off-line columns of spacing `2π/L` (`D = L/π`,
  `πD/2 = L/2`). -/
theorem onsetAperture_perturbedOffLineLatticeConfig_eq {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {ε : ℤ → ℝ} (hε : ∀ k : ℤ, |ε k| ≤ π / (2 * L))
    (hε_sum : Summable fun k : ℤ => |ε k|)
    (hridge : 2 * L * Real.exp (δ * L) * (∑' k : ℤ, |ε k|) ≤ 1) :
    onsetAperture (perturbedOffLineLatticeConfig hL hδ hδ' ε hε) = ((L / 2 : ℝ) : EReal) := by
  set Z := perturbedOffLineLatticeConfig hL hδ hδ' ε hε
  have hge : ((L / 2 : ℝ) : EReal) ≤ onsetAperture Z := by
    refine le_onsetAperture_of_windowPositiveAt (by positivity)
      (windowPositiveAt_perturbedOffLineLatticeConfig hL hδ hδ' hε hε_sum (by positivity) le_rfl ?_)
    have heq : 8 * (L / 2) ^ 2 * Real.exp (2 * δ * (L / 2)) * (∑' k : ℤ, |ε k|) =
        L * (2 * L * Real.exp (δ * L) * (∑' k : ℤ, |ε k|)) := by
      rw [show 2 * δ * (L / 2) = δ * L by ring]; ring
    rw [heq]
    exact mul_le_of_le_one_right hL.le hridge
  have hle : onsetAperture Z ≤ ((L / 2 : ℝ) : EReal) := by
    have hZ : TemperedConfig Z := temperedConfig_perturbedOffLineLatticeConfig hL hδ hδ' ε hε
    set ν : Unit → ℤ → ℂ := fun _ k => (((k : ℝ) * (2 * π / L) + ε k : ℝ) : ℂ) - I * δ
    have hν : ∀ j ∈ ({()} : Finset Unit), ∀ k : ℤ,
        ‖ν j k - k * ((2 * π / L : ℝ) : ℂ)‖ ≤ π / (2 * L) + 1 / 2 := by
      intro j _ k
      have heq : ν j k - (k : ℂ) * ((2 * π / L : ℝ) : ℂ) = (ε k : ℂ) - I * (δ : ℂ) := by
        dsimp only [ν]; push_cast; ring
      rw [heq]
      calc ‖(ε k : ℂ) - I * (δ : ℂ)‖
          ≤ ‖(ε k : ℂ)‖ + ‖I * (δ : ℂ)‖ := norm_sub_le _ _
        _ = |ε k| + |δ| := by
            rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul,
              Complex.norm_real, Real.norm_eq_abs]
        _ ≤ π / (2 * L) + 1 / 2 := by rw [abs_of_pos hδ]; linarith [hε k]
    have him : ∀ j ∈ ({()} : Finset Unit), ∀ k : ℤ, |(ν j k).im| ≤ 1 / 2 := by
      intro j _ k
      have him_eq : (ν j k).im = -δ := by simp [ν]
      rw [him_eq, abs_neg, abs_of_pos hδ]
      exact hδ'
    have hS : ∀ z ∈ Z.carrier,
        (∃ j ∈ ({()} : Finset Unit), ∃ k : ℤ, gammaOf z = ν j k ∨ gammaOf z = conj (ν j k)) ∨
          z ∈ (∅ : Finset ℂ) := by
      rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · refine Or.inl ⟨(), Finset.mem_singleton_self (), k, Or.inl ?_⟩
        rw [gammaOf_offLinePoint]
      · refine Or.inl ⟨(), Finset.mem_singleton_self (), k, Or.inr ?_⟩
        rw [gammaOf_offLinePoint]
        dsimp [ν]
        simp only [map_sub, Complex.conj_ofReal, map_mul, Complex.conj_I]
        push_cast; ring
    have hρ₀ : offLinePoint δ (((0 : ℤ) : ℝ) * (2 * π / L) + ε 0) ∈ Z.carrier :=
      Or.inl ⟨0, rfl⟩
    have hoff : (offLinePoint δ (((0 : ℤ) : ℝ) * (2 * π / L) + ε 0)).re ≠ 1 / 2 := by
      simp only [offLinePoint]; linarith
    have hbound := onsetAperture_le_half_pi_density_of_all_offLine_columns hZ ({()} : Finset Unit)
      (fun _ => 2 * π / L) (fun _ => π / (2 * L) + 1 / 2) (fun _ _ => by positivity)
      ν hν him ∅ hS hρ₀ hoff
    have hsum : π * ∑ _ ∈ ({()} : Finset Unit), (2 * π / L)⁻¹ = L / 2 := by
      rw [Finset.sum_singleton]; field_simp
    rwa [hsum] at hbound
  exact le_antisymm hle hge

/-! ### 4. The three structural dichotomies resolving Tests (1)–(3) and the six programme effects -/

/-- **Shallow dichotomy (`B21` vs `B22`):**
1. *Failure of naive `(V2)` on `DCI`-admissible coherent shallow clusters:* For `L ≤ k ≤ 20 L`,
   `multiplicityPairConfig` satisfies `DCI`'s unit-window bound `2kδ² ≤ 40δ²L` globally, yet is
   already visible (`onsetAperture < a`) whenever `3/2 < δ² a³` (`δ > √(3/2) a^{−3/2}`);
2. *Universal non-lattice shallow `(V2)` hiding:* Conversely, any tempered configuration `Z` over an
   `m₀`-multiplicity `2π/L` on-line lattice (`0 < a ≤ L/2`) whose off-line zeros have depth `≤ σ`
   and unit-window depth-squared mass `≤ W` satisfies `(a : EReal) ≤ onsetAperture Z` whenever
   `a² (2a + 2π) e^{2π} e^{2σa} W ≤ m₀ L` (`W ≲ L / a³`). -/
theorem shallow_coherence_vs_nonlattice_hiding_dichotomy :
    (∀ (k : ℕ) (hk : 1 ≤ k) {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ),
      L ≤ (k : ℝ) → (k : ℝ) ≤ 20 * L →
      ∀ {a : ℝ}, 0 < a → a ≤ L / 2 → 3 / 2 < δ ^ 2 * a ^ 3 →
        (∀ ρ ∈ (multiplicityPairConfig k hk hL hδ hδ' γ₀).carrier, |ρ.re - 1 / 2| ≤ δ) ∧
          2 * (k : ℝ) * δ ^ 2 ≤ 40 * δ ^ 2 * L ∧
          onsetAperture (multiplicityPairConfig k hk hL hδ hδ' γ₀) < (a : EReal)) ∧
    (∀ {Z : ZeroConfig} (_hZ : TemperedConfig Z) {L a σ W : ℝ},
      0 < L → 0 < a → a ≤ L / 2 → 0 ≤ σ →
      ∀ (m₀ : ℕ), Set.range (verticalLatticePoint L 0) ⊆ Z.carrier →
        (∀ k : ℤ, m₀ ≤ Z.mult (verticalLatticePoint L 0 k)) →
        (∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → |ρ.re - 1 / 2| ≤ σ) →
        (∀ (T : ℝ) (F : Finset ℂ),
          (∀ ρ ∈ F, ρ ∈ Z.carrier ∧ ρ.re ≠ 1 / 2 ∧ |ρ.im - T| ≤ 1) →
          ∑ ρ ∈ F, (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 ≤ W) →
        a ^ 2 * ((2 * a + 2 * π) * Real.exp (2 * π) * Real.exp (2 * σ * a)) * W ≤ (m₀ : ℝ) * L →
        WindowPositiveAt Z a ∧ (a : EReal) ≤ onsetAperture Z) :=
  ⟨fun k hk {_ _} hL hδ hδ' γ₀ hk1 hk2 {_} ha haL hsub =>
      dci_admissible_coherent_cluster_visible_at_sub_depth k hk hL hδ hδ' γ₀ hk1 hk2 ha haL hsub,
    fun {_} hZ {_ _ _ _} hL ha haL hσ m₀ hsub hmult hdepth hW hhide =>
      windowPositiveAt_of_onLineLattice_and_offLineDepthMass hZ hL ha haL hσ m₀ hsub hmult hdepth
        hW hhide⟩

/-- **Aperture–height duality dichotomy (`Σ28` / `Σ41`):**
1. *Unshielded doubly-exponential seeing:* Without deep collar shielding (outside zeros of depth
   `≤ σ`), `WindowPositiveAt Z a` excludes every coherent cluster violating the `e^{2(δ − σ)a}`
   exponential bound (reaching doubly-exponential height `|γ₀| ≍ exp(k e^{2(δ−σ)a}/(Cδa))`);
2. *Shielded single-exponential barrier at `δ = 1/a`:* Conversely, for every `a ≥ 2`, `L ≥ 4a`, and
   `k₀ : ℤ`, a finite biquadratic crystal packet contains an off-line zero of exact depth `1/a` at
   ordinate `2πk₀/L`, has finitely many off-line zeros, and satisfies `(a : EReal) ≤ onsetAperture Z`. -/
theorem aperture_height_duality_shielded_vs_unshielded :
    (∀ (Z : ZeroConfig) {A₀ : ℝ}, 1 ≤ A₀ →
      (∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) →
      ∀ {γ₀ a δ σ : ℝ}, 0 < δ → δ ≤ 1 / 2 → 2 ≤ δ * a → 0 ≤ σ →
        WindowPositiveAt Z a →
        ∀ S : Finset ℂ, S.Nonempty → (∀ ρ ∈ S, ρ ∈ Z.carrier) →
          (∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) → (∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a)) →
          (∀ ρ ∈ Z.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) →
          (1 / 2) * (∑ ρ ∈ S, (Z.mult ρ : ℝ)) * Real.exp (2 * (δ - σ) * a) ≤
            120 * 2 ^ 26 * A₀ * δ * (2 * a + 2 * π) * Real.exp (2 * π) *
              Real.log (|γ₀| + 1 / (4 * a) +
                3072 * 2 ^ 26 * A₀ * Real.log (|γ₀| + 3) * (50 * a) ^ 7 * Real.exp a + 6)) ∧
    (∀ {a L : ℝ}, 2 ≤ a → 4 * a ≤ L → ∀ k₀ : ℤ,
      ∃ Z : ZeroConfig, TemperedConfig Z ∧
        verticalLatticePoint L (1 / a) k₀ ∈ Z.carrier ∧
        (verticalLatticePoint L (1 / a) k₀).re - 1 / 2 = 1 / a ∧
        {ρ ∈ Z.carrier | ρ.re ≠ 1 / 2}.Finite ∧
        WindowPositiveAt Z a ∧ (a : EReal) ≤ onsetAperture Z) :=
  ⟨fun Z {_} hA₀ hloc {_ _ _ _} hδ hδ' hδa hσ hpos S hSne hSc hSδ hSγ hsea =>
      windowPositiveAt_global_sea_cluster_bound Z hA₀ hloc hδ hδ' hδa hσ hpos S hSne hSc hSδ hSγ
        hsea,
    fun ha2 haL k₀ => exists_hidden_inv_aperture_zero_above_single_exp ha2 haL k₀⟩

/-- **Split-column and perturbed-lattice dichotomy (`Γ36`, `Γ40`, `Π29`):**
1. *Exact `(g − ½)ℓ > (g/2)ℓ = πD/2` onset on mixed `2g`-column configurations (`g ≥ 2`):* Refutes
   `πD/2` for mixed column configurations and proves the split-column law `π D_on + (π/2) D_off`
   sharp;
2. *Single-defect fragility vs `ℓ¹` ridge stability (`Π29`):* Moving a single off-line pair of
   `offLineLatticeConfig` by `ε ∈ (0, π/L]` collapses `onsetAperture` below every `a ≤ L/2` (`2 ≤ δa`)
   with `960 · 2^{26} δ L < ε² a² e^{2δa}`, whereas `ℓ¹` perturbations with
   `2 L e^{δL} ∑_k |ε_k| ≤ 1` preserve the exact onset aperture `L/2`. -/
theorem split_column_and_perturbed_lattice_dichotomy :
    (∀ {g : ℕ} (hg : 2 ≤ g) {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2),
      4 * (((2 * g - 1 : ℕ) : ℝ) - 1) *
        (Real.cosh (δ * (((2 * g - 1 : ℕ) : ℝ) * ℓ)) - 1) ≤ ((2 * g - 1 : ℕ) : ℝ) →
      onsetAperture (mixedGenusColumnConfig hg hℓ hδ hδ') = ((((g : ℝ) - 1 / 2) * ℓ : ℝ) : EReal) ∧
        ((((g : ℝ) / 2) * ℓ : ℝ) : EReal) < onsetAperture (mixedGenusColumnConfig hg hℓ hδ hδ')) ∧
    (∀ {L δ ε a : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hε : 0 < ε) (hεL : ε ≤ π / L),
      a ≤ L / 2 → 2 ≤ δ * a → 960 * 2 ^ 26 * δ * L < ε ^ 2 * a ^ 2 * Real.exp (2 * δ * a) →
      onsetAperture (singleDefectOffLineLattice hL hδ hδ' hε hεL) < (a : EReal)) ∧
    (∀ {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {ε : ℤ → ℝ}
      (hε : ∀ k : ℤ, |ε k| ≤ π / (2 * L)), Summable (fun k : ℤ => |ε k|) →
      2 * L * Real.exp (δ * L) * (∑' k : ℤ, |ε k|) ≤ 1 →
      onsetAperture (perturbedOffLineLatticeConfig hL hδ hδ' ε hε) = ((L / 2 : ℝ) : EReal)) :=
  ⟨fun {_} hg {_ _} hℓ hδ hδ' hsmall =>
      onsetAperture_mixedGenusColumnConfig_eq hg hℓ hδ hδ' hsmall,
    fun hL hδ hδ' hε hεL haL hδa hdet =>
      onsetAperture_singleDefectOffLineLattice_lt hL hδ hδ' hε hεL haL hδa hdet,
    fun {_ _} hL hδ hδ' {_} hε hsum hridge =>
      onsetAperture_perturbedOffLineLatticeConfig_eq hL hδ hδ' hε hsum hridge⟩

/-- **Unconditional `ζ` package of programme consequences (`P1`, `AHD`, `B18`, `B21`, `Σ28`).**
Collects the unconditional statements on `zetaZeroConfig` proven across the visibility modules:
1. `P1` explicit zero-location output at `enlargedWeilFloorAperture`;
2. `AHD` critical-threshold equivalence `windowThreshold A = ⊤ ↔ A/2 ≤ onsetAperture zetaZeroConfig`;
3. Closed-endpoint `1/R` excluded-depth law for `((R : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig`;
4. Logarithmic contact-law power-saving cluster bound (`c log T ≤ onsetAperture zetaZeroConfig`). -/
theorem zeta_programme_consequences_of_window_visibility :
    (((enlargedWeilFloorAperture : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig) ∧
      (∀ {A : ℝ}, 0 ≤ A →
        (windowThreshold A = ⊤ ↔ ((A / 2 : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig)) ∧
      (∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ R : ℝ, Real.exp 6 ≤ R →
        ((R : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig →
        ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| → |ρ.im| ≤ zetaClusterHorizonHeight A₀ R →
          |ρ.re - 1 / 2| < 1 / R) ∧
      (∃ A₀ : ℝ, 1 ≤ A₀ ∧
        ∀ {c T γ₀ δ σ : ℝ}, 0 < c → 3 ≤ T → |γ₀| ≤ T →
          0 < δ → δ ≤ 1 / 2 → 2 ≤ δ * (c * Real.log T) → 0 ≤ σ →
          ((c * Real.log T : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig →
          ∀ S : Finset ℂ, S.Nonempty → (∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier) →
            (∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) →
            (∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * (c * Real.log T))) →
            (∀ ρ ∈ zetaZeroConfig.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) →
            (1 / 2) * (∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ)) *
                T ^ (2 * c * (δ - σ)) ≤
              120 * 2 ^ 26 * A₀ * δ * (2 * (c * Real.log T) + 2 * π) * Real.exp (2 * π) *
                Real.log (T + 1 / (4 * (c * Real.log T)) +
                  3072 * 2 ^ 26 * A₀ * Real.log (T + 3) *
                    (50 * (c * Real.log T)) ^ 7 * T ^ c + 6)) :=
  ⟨enlargedWeilFloorAperture_le_onsetAperture_zeta,
    fun hA => windowThreshold_eq_top_iff_le_onsetAperture hA,
    zeta_abs_re_sub_half_lt_of_le_onsetAperture,
    contact_law_log_scale_cluster_bound⟩

end GaloisForLFunctions.WindowVisibilityLaw
