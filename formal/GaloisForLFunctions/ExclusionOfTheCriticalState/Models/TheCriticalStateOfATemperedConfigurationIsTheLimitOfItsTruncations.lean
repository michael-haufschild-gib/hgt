import GaloisForLFunctions.ExclusionOfTheCriticalState.Models.TheCriticalStateOfATemperedConfigurationIsALimitOfZeroExponentials

/-!
# The critical state of a tempered configuration is the limit of its truncations

Truncating the positive series of a layered energy to finitely many terms (`LayeredEnergy.truncate`)
leaves a form on finitely many functionals plus the finite-rank layer. Its ground state is explicit:
by the Euler–Lagrange equation it is a finite combination of the retained vectors and the layer
vectors (`mem_span_of_groundState`).

**Convergence** (`exists_tendsto_truncated_groundState`). Along an exhausting increasing sequence of
truncations the ground energies `λ_N` increase to the ground energy `λ` of the full form, and a
subsequence of the truncated ground states converges in norm to a ground state of the full form.
Mechanism: `λ_N ≤ λ` since truncation lowers the energy; a weak limit `F*` of the unit truncated states
has every truncated energy `≤ lim λ_N` (weak continuity of each finite truncation), hence full energy
`≤ lim λ_N ≤ λ < 0`; minimality of `λ` forces `‖F*‖ = 1` and equality, and weak convergence with
convergence of norms is norm convergence.

**Finite configurations** (`exists_configCriticalState_finite_explicit`). With a finite carrier the
critical state is itself a finite exponential sum at the shifted zeros.

**Tempered configurations** (`exists_configCriticalState_truncations`). The carrier of a zero
configuration is countable, so the on-line points can be exhausted by finite sets. The critical state
of a conjugation-invariant tempered configuration with a finite nonempty off-line layer is the norm
limit of the critical states of the truncated configurations, each a finite exponential sum
`Σ c_z e^{(z+8)u} cos(Im z · u) + d_z e^{(z+8)u} sin(Im z · u)` over finitely many shifted zeros
`z = ±(ρ − ½)`, and the critical ratios converge.
-/

noncomputable section
open Set Filter Topology Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

namespace GroundState

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι κ : Type*}

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

namespace LayeredEnergy

variable (L : LayeredEnergy E ι κ)

/-- The truncation keeping the series terms indexed by `s` and the whole layer. -/
def truncate (s : Finset ι) : LayeredEnergy E s κ where
  w j := L.w j
  a j := L.a j
  b j := L.b j
  w_nonneg j := L.w_nonneg j
  v := L.v
  p := L.p
  q := L.q

theorem truncate_admissible (s : Finset ι) (G : E) : (L.truncate s).Admissible G :=
  Summable.of_finite

theorem energy_truncate [Fintype κ] (s : Finset ι) (G : E) :
    (L.truncate s).energy G = ∑ j ∈ s, L.term G j + L.layer G := by
  show (∑' j : s, L.term G j) + L.layer G = _
  rw [Finset.tsum_subtype s (fun j => L.term G j)]

/-- Truncation lowers the energy. -/
theorem energy_truncate_le [Fintype κ] {G : E} (hG : L.Admissible G) (s : Finset ι) :
    (L.truncate s).energy G ≤ L.energy G := by
  rw [energy_truncate]
  have h := hG.sum_le_tsum s (fun j _ => L.term_nonneg G j)
  unfold energy series
  linarith

theorem energy_truncate_mono [Fintype κ] {s t : Finset ι} (hst : s ⊆ t) (G : E) :
    (L.truncate s).energy G ≤ (L.truncate t).energy G := by
  rw [energy_truncate, energy_truncate]
  have h := Finset.sum_le_sum_of_subset_of_nonneg hst (fun j _ _ => L.term_nonneg G j)
  linarith

/-- A finite truncation is weakly continuous. -/
theorem tendsto_energy_truncate [Fintype κ] (s : Finset ι) {u : ℕ → E} {F : E}
    (hu : ∀ y : E, Tendsto (fun n => ⟪u n, y⟫) atTop (𝓝 ⟪F, y⟫)) :
    Tendsto (fun n => (L.truncate s).energy (u n)) atTop (𝓝 ((L.truncate s).energy F)) := by
  simp only [energy_truncate]
  refine (tendsto_finsetSum s fun j _ => ?_).add (L.tendsto_layer hu)
  have ha : Tendsto (fun n => ⟪L.a j, u n⟫) atTop (𝓝 ⟪L.a j, F⟫) := by
    rw [real_inner_comm F (L.a j)]; exact (hu (L.a j)).congr fun n => real_inner_comm (L.a j) (u n)
  have hb : Tendsto (fun n => ⟪L.b j, u n⟫) atTop (𝓝 ⟪L.b j, F⟫) := by
    rw [real_inner_comm F (L.b j)]; exact (hu (L.b j)).congr fun n => real_inner_comm (L.b j) (u n)
  exact ((ha.pow 2).add (hb.pow 2)).const_mul _

/-- A countable index set is exhausted by an increasing sequence of finite sets. -/
theorem exists_exhaustion (ι : Type*) [Countable ι] :
    ∃ s : ℕ → Finset ι, Monotone s ∧ ∀ j, ∃ N, j ∈ s N := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat ι
  refine ⟨fun N => (Finset.range N).preimage f (fun _ _ _ _ h => hf h),
    fun M N hMN j hj => ?_, fun j => ⟨f j + 1, ?_⟩⟩
  · simp only [Finset.mem_preimage, Finset.mem_range] at hj ⊢
    omega
  · simp

/-- **Truncated ground states converge to a ground state.** -/
theorem exists_tendsto_truncated_groundState [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] [Fintype κ] {F₀ : E} (hF₀ : L.Admissible F₀)
    (hneg : L.energy F₀ < 0) {s : ℕ → Finset ι} (hs : Monotone s) (hexh : ∀ j, ∃ N, j ∈ s N) :
    ∃ (lam : ℝ) (F : E) (lamN : ℕ → ℝ) (FN : ℕ → E) (φ : ℕ → ℕ),
      lam < 0 ∧ L.Admissible F ∧ ‖F‖ = 1 ∧ L.energy F = lam ∧
      (∀ G, L.Admissible G → lam * ‖G‖ ^ 2 ≤ L.energy G) ∧
      (∀ N, lamN N < 0 ∧ ‖FN N‖ = 1 ∧ (L.truncate (s N)).energy (FN N) = lamN N ∧
        (∀ G, lamN N * ‖G‖ ^ 2 ≤ (L.truncate (s N)).energy G) ∧
        FN N ∈ Submodule.span ℝ (Set.range (L.truncate (s N)).a ∪
          Set.range (L.truncate (s N)).b ∪ Set.range L.p ∪ Set.range L.q)) ∧
      StrictMono φ ∧ Tendsto lamN atTop (𝓝 lam) ∧ Tendsto (fun n => FN (φ n)) atTop (𝓝 F) := by
  classical
  obtain ⟨Fg, hFga, hFg1, hFgneg, hFgmin⟩ := L.exists_groundState_of_negative hF₀ hneg
  -- ground states of the truncations
  have htr : ∀ N, ∃ G : E, ‖G‖ = 1 ∧ (L.truncate (s N)).energy G < 0 ∧
      ∀ H : E, (L.truncate (s N)).energy G * ‖H‖ ^ 2 ≤ (L.truncate (s N)).energy H := by
    intro N
    obtain ⟨G, -, hG1, hGneg, hGmin⟩ := (L.truncate (s N)).exists_groundState_of_negative
      (L.truncate_admissible _ F₀) (lt_of_le_of_lt (L.energy_truncate_le hF₀ (s N)) hneg)
    exact ⟨G, hG1, hGneg, fun H => hGmin H (L.truncate_admissible _ H)⟩
  choose FN hFN1 hFNneg hFNmin using htr
  -- the truncated ground energies increase and stay below `λ`
  have hle_g : ∀ N, (L.truncate (s N)).energy (FN N) ≤ L.energy Fg := fun N => by
    have h1 := hFNmin N Fg
    rw [hFg1, one_pow, mul_one] at h1
    exact h1.trans (L.energy_truncate_le hFga (s N))
  have hmono : Monotone fun N => (L.truncate (s N)).energy (FN N) := fun M N hMN => by
    have h1 := hFNmin M (FN N)
    rw [hFN1 N, one_pow, mul_one] at h1
    exact h1.trans (L.energy_truncate_mono (hs hMN) (FN N))
  have hbdd : BddAbove (Set.range fun N => (L.truncate (s N)).energy (FN N)) :=
    ⟨L.energy Fg, by rintro _ ⟨N, rfl⟩; exact hle_g N⟩
  have hconv := tendsto_atTop_ciSup hmono hbdd
  have hsup_le : (⨆ N, (L.truncate (s N)).energy (FN N)) ≤ L.energy Fg := ciSup_le hle_g
  have hle_sup : ∀ N, (L.truncate (s N)).energy (FN N) ≤ ⨆ N, (L.truncate (s N)).energy (FN N) :=
    fun N => le_ciSup hbdd N
  -- a weak limit of the truncated states
  obtain ⟨F, φ, hφ, hF1, hweak⟩ := exists_weaklyConvergent_subseq FN 1 (fun n => (hFN1 n).le)
  have hM : ∀ M, (L.truncate (s M)).energy F ≤ ⨆ N, (L.truncate (s N)).energy (FN N) := by
    intro M
    refine le_of_tendsto (L.tendsto_energy_truncate (s M) (u := fun n => FN (φ n)) hweak)
      (eventually_atTop.mpr ⟨M, fun n hn => ?_⟩)
    exact (L.energy_truncate_mono (hs (hn.trans (hφ.id_le n))) _).trans (hle_sup (φ n))
  -- the weak limit is admissible with energy below the limit of the `λ_N`
  have hfin : ∀ t : Finset ι, ∃ M, t ⊆ s M := by
    choose Nj hNj using hexh
    exact fun t => ⟨t.sup Nj, fun j hj => hs (Finset.le_sup hj) (hNj j)⟩
  have hpart : ∀ t : Finset ι,
      ∑ j ∈ t, L.term F j ≤ (⨆ N, (L.truncate (s N)).energy (FN N)) - L.layer F := by
    intro t
    obtain ⟨M, hM'⟩ := hfin t
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hM' (fun j _ _ => L.term_nonneg F j)
    have h2 := hM M
    rw [energy_truncate] at h2
    linarith
  have hFa : L.Admissible F := summable_of_sum_le (L.term_nonneg F) hpart
  have hEF : L.energy F ≤ ⨆ N, (L.truncate (s N)).energy (FN N) := by
    have h := Real.tsum_le_of_sum_le (L.term_nonneg F) hpart
    have e : L.energy F = (∑' j, L.term F j) + L.layer F := rfl
    rw [e]
    linarith
  -- minimality of `λ` forces a unit ground state
  have hge := hFgmin F hFa
  have hF1' : ‖F‖ = 1 := by
    have h1 : L.energy Fg * ‖F‖ ^ 2 ≤ L.energy Fg := by linarith
    have h2 : 1 ≤ ‖F‖ ^ 2 := by nlinarith
    exact le_antisymm hF1 (by nlinarith [norm_nonneg F])
  rw [hF1', one_pow, mul_one] at hge
  have hEq : L.energy F = L.energy Fg := le_antisymm (by linarith) hge
  have hsup_eq : (⨆ N, (L.truncate (s N)).energy (FN N)) = L.energy Fg :=
    le_antisymm hsup_le (by linarith)
  -- weak convergence with convergence of norms
  have hstrong : Tendsto (fun n => FN (φ n)) atTop (𝓝 F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h := hweak F
    rw [real_inner_self_eq_norm_sq, hF1'] at h
    have hsq : Tendsto (fun n => ‖FN (φ n) - F‖ ^ 2) atTop (𝓝 0) := by
      have e : ∀ n, ‖FN (φ n) - F‖ ^ 2 = 2 - 2 * ⟪FN (φ n), F⟫ := fun n => by
        rw [@norm_sub_sq_real, hFN1, hF1']; ring
      simp_rw [e]
      simpa using (h.const_mul 2).const_sub 2
    simpa [Real.sqrt_sq (norm_nonneg _)] using hsq.sqrt
  refine ⟨L.energy Fg, F, fun N => (L.truncate (s N)).energy (FN N), FN, φ, hFgneg, hFa, hF1',
    hEq, hFgmin, fun N => ⟨hFNneg N, hFN1 N, rfl, hFNmin N, ?_⟩, hφ, hsup_eq ▸ hconv, hstrong⟩
  exact (L.truncate (s N)).mem_span_of_groundState (hFNneg N).ne
    (by rw [hFN1 N, one_pow, mul_one]) (fun G _ => hFNmin N G)

end LayeredEnergy

end GroundState

namespace ModelStates

open GroundState
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

/-- The carrier of a zero configuration is countable: finitely many points in each unit window of
ordinates. -/
theorem countable_carrier (Z : ZeroConfig) : Countable Z.carrier := by
  have h : Z.carrier = ⋃ k : ℤ, Z.carrier ∩ {ρ | (k : ℝ) < ρ.im ∧ ρ.im ≤ k + 1} := by
    ext ρ
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hρ
      refine ⟨⌈ρ.im⌉ - 1, hρ, ?_, ?_⟩ <;> push_cast <;>
        linarith [Int.ceil_lt_add_one ρ.im, Int.le_ceil ρ.im]
    · rintro ⟨k, hρ, -⟩
      exact hρ
  have hc : Z.carrier.Countable := by
    rw [h]
    exact Set.countable_iUnion fun k => (Z.finite_window k (k + 1)).countable
  exact hc.to_subtype

variable {Z : ZeroConfig}

/-- **The critical state is the limit of the explicit critical states of the truncations.** -/
theorem exists_configCriticalState_truncations (hZ : TemperedConfig Z)
    (hfin : (offLineSet Z).Finite)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ (s : ℕ → Finset (OnLineIdx Z)) (a : ℝ) (F : ConfSpace) (aN : ℕ → ℝ) (FN : ℕ → ConfSpace)
      (φ : ℕ → ℕ), Monotone s ∧ (∀ j, ∃ N, j ∈ s N) ∧
      0 < a ∧ (configEnergy hfin).Admissible F ∧ ‖F‖ = 1 ∧
      (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
      (∀ G, (configEnergy hfin).Admissible G →
        0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2) ∧
      (∀ N, 0 < aN N ∧ ‖FN N‖ = 1 ∧
        ((configEnergy hfin).truncate (s N)).energy (FN N) + aN N = 0 ∧
        (∀ G, 0 ≤ ((configEnergy hfin).truncate (s N)).energy G + aN N * ‖G‖ ^ 2) ∧
        ∃ T : Set ConfSpace, T.Finite ∧ T ⊆ zeroExponentials Z ∧ FN N ∈ Submodule.span ℝ T) ∧
      StrictMono φ ∧ Tendsto aN atTop (𝓝 a) ∧ Tendsto (fun n => FN (φ n)) atTop (𝓝 F) := by
  haveI : Countable Z.carrier := countable_carrier Z
  haveI : Countable (OnLineIdx Z) := by unfold OnLineIdx; infer_instance
  obtain ⟨s, hs, hexh⟩ := LayeredEnergy.exists_exhaustion (OnLineIdx Z)
  obtain ⟨f, hf, hneg⟩ := exists_halfLineTest_neg hZ hconj hρ₀ hre
  obtain ⟨hadm, heq⟩ := configEnergy_toLp_eq_re_W hZ hfin hf
  obtain ⟨lam, F, lamN, FN, φ, hlam, hFa, hF1, hEF, hmin, hN, hφ, hlim, hconv⟩ :=
    (configEnergy hfin).exists_tendsto_truncated_groundState hadm (by rw [heq]; exact hneg) hs hexh
  refine ⟨s, -lam, F, fun N => -lamN N, FN, φ, hs, hexh, by linarith, hFa, hF1,
    by rw [hEF, hF1]; ring, fun G hG => by have := hmin G hG; linarith, fun N => ?_, hφ,
    hlim.neg, hconv⟩
  obtain ⟨hlamN, hFN1, hEN, hminN, hspan⟩ := hN N
  refine ⟨by linarith, hFN1, by rw [hEN]; ring, fun G => by have := hminN G; linarith, _, ?_, ?_,
    hspan⟩
  · exact (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)
  · rintro v (((⟨ρ, rfl⟩ | ⟨ρ, rfl⟩) | ⟨x, rfl⟩) | ⟨x, rfl⟩)
    · exact layerVectors_subset_zeroExponentials hfin (Or.inl (Or.inl (Or.inl ⟨ρ.1, rfl⟩)))
    · exact layerVectors_subset_zeroExponentials hfin (Or.inl (Or.inl (Or.inr ⟨ρ.1, rfl⟩)))
    · exact layerVectors_subset_zeroExponentials hfin (Or.inl (Or.inr ⟨x, rfl⟩))
    · exact layerVectors_subset_zeroExponentials hfin (Or.inr ⟨x, rfl⟩)

/-- **Finite configurations: the critical state is an explicit exponential sum.** If the carrier is
finite, every series index is a finite set and the critical state is a finite combination of the
exponentials at the shifted zeros, with the critical-ratio eigen-equation as coefficients. -/
theorem exists_configCriticalState_finite_explicit (hZ : TemperedConfig Z)
    (hcar : Z.carrier.Finite)
    (hconj : ∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier ∧ Z.mult (conj ρ) = Z.mult ρ)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hre : ρ₀.re ≠ 1 / 2) :
    ∃ hfin : (offLineSet Z).Finite, ∃ (a : ℝ) (F : ConfSpace), 0 < a ∧ ‖F‖ = 1 ∧
      (configEnergy hfin).energy F + a * ‖F‖ ^ 2 = 0 ∧
      (∀ G : ConfSpace, 0 ≤ (configEnergy hfin).energy G + a * ‖G‖ ^ 2) ∧
      ∃ T : Set ConfSpace, T.Finite ∧ T ⊆ zeroExponentials Z ∧ F ∈ Submodule.span ℝ T := by
  have hfin : (offLineSet Z).Finite := hcar.subset fun ρ h => h.1
  haveI : Finite Z.carrier := hcar.to_subtype
  haveI : Finite (OnLineIdx Z) := by unfold OnLineIdx; infer_instance
  obtain ⟨a, F, ha, -, hF1, hEq, hmin⟩ := exists_configCriticalState hZ hfin hconj hρ₀ hre
  have hadm : ∀ G : ConfSpace, (configEnergy hfin).Admissible G := fun G => Summable.of_finite
  refine ⟨hfin, a, F, ha, hF1, hEq, fun G => hmin G (hadm G), _, ?_,
    layerVectors_subset_zeroExponentials hfin,
    (configEnergy hfin).mem_span_of_groundState (lam := -a) (neg_ne_zero.mpr ha.ne') (by linarith)
      (fun G hG => by have := hmin G hG; linarith)⟩
  exact (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
    (Set.finite_range _)

#print axioms exists_configCriticalState_truncations
#print axioms exists_configCriticalState_finite_explicit

end ModelStates

end GaloisForLFunctions.ExclusionOfTheCriticalState
