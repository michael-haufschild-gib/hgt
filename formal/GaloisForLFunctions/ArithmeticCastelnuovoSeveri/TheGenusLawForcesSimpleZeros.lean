import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheGenusFunctionReadsTheResolvedZeros
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LandauWidomNearRadicalLaw

/-!
# The genus law forces simple, resolved zeros

The *genus function* of `ℤ` at level `L` and threshold `ε` is
`g(L, ε) = max {dim V : V ⊆ Hodge-class tests at level L, ‖W(f,f)‖ ≤ ε ∫|f|² on V}`
(`genusFunction`); it is finite by `zeta_near_radical_finrank_le`. The *genus law* asked of it is
`g(L, ε_η(L)) ≤ (2 + η) e^{2L}` for large `L`, at the natural threshold
`ε_η(L) = exp(−η² e^{2L}/(300L))` where the lower bound `(2 − η)e^{2L}` is proved.

**The genus law is not a time–frequency statement: it is a statement about the multiplicities and
the mutual distances of the zeros of `ζ`.** Weil's form reads a zero through the value of the
transform there, so the construction of the near radical spends one constraint per distinct zero,
and even one per cluster of zeros closer than the resolution of the threshold. Hence:

* `exists_nearRadical_blind`, `genusFunction_ge_distinct`:
  `g(L, ε_η(L)) ≥ (2 − η)e^{2L} + 2(N(0,T) − N_d(0,T))` at `T = 2πe^{2(L − η/8)}`, where `N` counts
  with multiplicity and `N_d` counts distinct zeros; the constructed space is blind to every zero
  of height `≤ T`.
* `genusFunction_ge_of_net`: `g(L, 2ε_η(L)) ≥ (2 − η)e^{2L} + 2N(0,T) − #S` for every finite set `S`
  of zeros within `exp(−η²e^{2L}/(100L))` of every zero of height `≤ T`.
* `multiplicity_excess_le_of_genus_law`: the genus law at one `η` gives
  `N(0,T) − N_d(0,T) ≤ ηT` for all large `T`.
* `nonsimple_le_of_genus_law`, `tendsto_simple_ratio_of_genus_law`: the genus law gives
  `N(0,T) − N^s(0,T) ≤ 2ηT`, i.e. all but `o(T)` of the zeros of `ζ` up to height `T` are simple,
  and the proportion of simple zeros tends to `1` (at rate `O(1/log T)`).
* `cover_deficiency_le_of_genus_law`: the genus law gives, for every finite set `S` of zeros within
  `exp(−η²T/(40 log T))` of every zero of height `≤ T`, `#S ≥ 2N(0,T) − ηT`: all but `o(T)` zeros
  are simple *and* isolated at the scale `exp(−η²T/(40 log T))`.

The unconditional knowledge in the corpus is that at least two thirds of the zeros are simple and
critical (`RHTower.two_thirds_simpleCritical_epsilon`); the genus law would raise this to all but
`o(T)`. So the upper Landau–Widom half of the genus law lies beyond time–frequency concentration
and zero counting: any proof of it proves that the zeros of `ζ` are almost all simple at rate
`1/log T`, a statement not known today. The dimension of the near radical of Weil's form at degree
`a` is at least the Shannon surplus against the *resolved* zeros; it is `(2 + o(1))e^{2a}` only if
the zeros are resolved at the doubly exponential scale up to `o(T)` exceptions.

The characterization half of the question holds for the constructed space
(`exists_nearRadical_blind`): every element of the constructed near radical has transform vanishing
at every zero of height `≤ T`.
-/

open Complex MeasureTheory Set Filter Topology Zeta23 RHTower
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ### The genus function -/

/-- The Hodge class at level `L`: `C²` tests supported in `[−L, L]` whose transform vanishes at the
poles `±i/2`. -/
def HodgeClass (L : ℝ) (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-L) L ∧ paperFT f (I / 2) = 0 ∧ paperFT f (-(I / 2)) = 0

/-- A near-radical subspace at level `L` and threshold `ε`: Hodge-class tests on which
`‖W(f, f)‖ ≤ ε ∫|f|²`. -/
def IsNearRadical (L ε : ℝ) (V : Submodule ℂ (ℝ → ℂ)) : Prop :=
  (∀ f ∈ V, HodgeClass L f) ∧ ∀ f ∈ V, ‖zetaZeroConfig.W f f‖ ≤ ε * ∫ u, ‖f u‖ ^ 2

/-- **The genus function of `ℤ`**: the largest dimension of a near-radical subspace at level `L`
and threshold `ε`. -/
def genusFunction (L ε : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ), IsNearRadical L ε V ∧ Module.finrank ℂ V = n}

/-- The natural threshold at level `L` and parameter `η`: `exp(−η² e^{2L}/(300L))`. -/
def naturalThreshold (η L : ℝ) : ℝ := Real.exp (-(η ^ 2 * Real.exp (2 * L) / (300 * L)))

/-- The Landau height of the construction at level `L`: `T_η(L) = 2π e^{2(L − η/8)}`. -/
def landauHeight (η L : ℝ) : ℝ := 2 * π * Real.exp (2 * (L - η / 8))

/-- The net scale at level `L`: `exp(−η² e^{2L}/(100L))`. -/
def netScale (η L : ℝ) : ℝ := Real.exp (-(η ^ 2 * Real.exp (2 * L) / (100 * L)))

theorem naturalThreshold_pos (η L : ℝ) : 0 < naturalThreshold η L := Real.exp_pos _

theorem netScale_pos (η L : ℝ) : 0 < netScale η L := Real.exp_pos _

theorem landauHeight_pos (η L : ℝ) : 0 < landauHeight η L := by unfold landauHeight; positivity

/-- Near-radical dimensions are bounded (`zeta_near_radical_finrank_le`). -/
theorem genus_set_bddAbove {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) :
    BddAbove {n : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ), IsNearRadical L ε V ∧ Module.finrank ℂ V = n} := by
  refine ⟨(lowGridOf (horizonFreqEps L ε) L).card, ?_⟩
  rintro n ⟨V, ⟨hV, hW⟩, rfl⟩
  by_cases hfin : FiniteDimensional ℂ V
  · exact zeta_near_radical_finrank_le hL hε V (fun f hf => hV f hf) hW
  · rw [Module.finrank_of_infinite_dimensional hfin]; exact Nat.zero_le _

/-- Every near-radical subspace has dimension at most the genus function. -/
theorem finrank_le_genusFunction {L ε : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε)
    {V : Submodule ℂ (ℝ → ℂ)} (hV : IsNearRadical L ε V) :
    Module.finrank ℂ V ≤ genusFunction L ε :=
  le_csSup (genus_set_bddAbove hL hε) ⟨V, hV, rfl⟩

/-- A uniform bound on near-radical dimensions bounds the genus function. -/
theorem genusFunction_le {L ε : ℝ} {m : ℕ}
    (h : ∀ V : Submodule ℂ (ℝ → ℂ), IsNearRadical L ε V → Module.finrank ℂ V ≤ m) :
    genusFunction L ε ≤ m :=
  csSup_le' (by rintro n ⟨V, hV, rfl⟩; exact h V hV)

/-- The genus function is monotone in the threshold. -/
theorem genusFunction_mono {L ε ε' : ℝ} (hL : 0 ≤ L) (hε : 0 ≤ ε) (hεε' : ε ≤ ε') :
    genusFunction L ε ≤ genusFunction L ε' := by
  refine genusFunction_le fun V ⟨hV, hW⟩ => finrank_le_genusFunction hL (hε.trans hεε') ⟨hV, ?_⟩
  intro f hf
  refine (hW f hf).trans (mul_le_mul_of_nonneg_right hεε' ?_)
  exact integral_nonneg fun _ => sq_nonneg _

/-! ### Distinct zeros of bounded height -/

/-- **Distinct zeros up to height `T`, against the distinct count.**
`#{ρ : |Im ρ| ≤ T} ≤ 2N_d(0,T) + c₀`, with `c₀` the number of real zeros. -/
theorem ncard_lowZeros_le_two_mul_Nd : ∃ c₀ : ℕ, ∀ T : ℝ, 0 ≤ T →
    (lowZeros T).ncard ≤ 2 * zetaZeroConfig.Nd 0 T + c₀ := by
  set Z₀ : Set ℂ := zetaZeroConfig.carrier ∩ {ρ | ρ.im = 0} with hZ₀
  have hZ₀fin : Z₀.Finite := (zetaZeroConfig.window_finite (-1) 0).subset fun ρ hρ =>
    ⟨hρ.1, by rw [hρ.2]; norm_num, by rw [hρ.2]⟩
  refine ⟨Z₀.ncard, fun T hT => ?_⟩
  set A := zetaZeroConfig.window 0 T with hA
  have hAfin : A.Finite := zetaZeroConfig.window_finite 0 T
  have hsub : lowZeros T ⊆ (A ∪ (starRingEnd ℂ) '' A) ∪ Z₀ := by
    intro ρ hρ
    rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
    · left; right
      refine ⟨(starRingEnd ℂ) ρ, ⟨conj_mem_zetaCarrier hρ.1, ?_, ?_⟩, by simp⟩
      · simp only [Complex.conj_im]; linarith
      · simp only [Complex.conj_im]; linarith [(abs_le.mp hρ.2).1]
    · right; exact ⟨hρ.1, hzero⟩
    · left; left; exact ⟨hρ.1, hpos, (abs_le.mp hρ.2).2⟩
  have hfin : ((A ∪ (starRingEnd ℂ) '' A) ∪ Z₀).Finite :=
    (hAfin.union (hAfin.image _)).union hZ₀fin
  have h1 := Set.ncard_le_ncard hsub hfin
  have h2 := Set.ncard_union_le (A ∪ (starRingEnd ℂ) '' A) Z₀
  have h3 := Set.ncard_union_le A ((starRingEnd ℂ) '' A)
  have h4 : ((starRingEnd ℂ) '' A).ncard ≤ A.ncard := Set.ncard_image_le hAfin
  have h5 : A.ncard = zetaZeroConfig.Nd 0 T := rfl
  omega

/-- `2N_d ≤ N + N^s`: a distinct zero counts twice against once with multiplicity plus once if
simple, since `2 − [m = 1] ≤ m` for every `m ≥ 1`. -/
theorem two_mul_Nd_le_N_add_Ns (Z : ZeroConfig) (T₁ T₂ : ℝ) :
    2 * Z.Nd T₁ T₂ ≤ Z.N T₁ T₂ + Z.Ns T₁ T₂ := by
  classical
  have hfin : (Z.window T₁ T₂).Finite := Z.window_finite T₁ T₂
  have hNd : Z.Nd T₁ T₂ = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
  have hN : Z.N T₁ T₂ = ∑ ρ ∈ hfin.toFinset, Z.mult ρ := by
    unfold ZeroConfig.N; exact finsum_mem_eq_finite_toFinset_sum _ hfin
  have hNs : Z.Ns T₁ T₂ = (hfin.toFinset.filter fun ρ => Z.mult ρ = 1).card := by
    have e : Z.window T₁ T₂ ∩ Z.simple = ↑(hfin.toFinset.filter fun ρ => Z.mult ρ = 1) := by
      ext ρ
      simp [ZeroConfig.simple, Set.Finite.mem_toFinset]
    unfold ZeroConfig.Ns
    rw [e, Set.ncard_coe_finset]
  rw [hNd, hN, hNs, Finset.card_filter, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hm : 1 ≤ Z.mult ρ :=
    Z.one_le_mult ρ (Z.window_subset_carrier T₁ T₂ (hfin.mem_toFinset.mp hρ))
  split_ifs with h <;> omega

/-! ### The refined lower bounds -/

/-- **The constructed near radical is blind to the zeros below the Landau height.** For every
`0 < η ≤ 1` and all large `L` there is a near-radical subspace `V` at threshold `ε_η(L)` with
`dim V ≥ (2 − η)e^{2L} + 2(N(0,T) − N_d(0,T))`, `T = 2πe^{2(L − η/8)}`, every element of which has
transform vanishing at every zero of height `≤ T`. -/
theorem exists_nearRadical_blind {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      ∃ V : Submodule ℂ (ℝ → ℂ), IsNearRadical L (naturalThreshold η L) V ∧
        (2 - η) * Real.exp (2 * L) +
          2 * ((zetaZeroConfig.N 0 (landauHeight η L) : ℝ) -
            zetaZeroConfig.Nd 0 (landauHeight η L)) ≤ (Module.finrank ℂ V : ℝ) ∧
        ∀ f ∈ V, ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ landauHeight η L →
          paperFT f (gammaOf ρ) = 0 := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨CR, T₁, hCR, hT₁, hcount⟩ := zeroCount_upper
  obtain ⟨c₀, hlow⟩ := ncard_lowZeros_le_two_mul_Nd
  have hpi := Real.pi_pos
  have e1 := eventually_mul_pow_four_le_exp (K := η / 4) (by positivity) (3 + c₀ + 8 * CR)
  have e2 := eventually_mul_pow_four_le_exp (K := η ^ 2) (by positivity)
    (1000 * (4800 * A₀ + 12))
  have e3 := eventually_mul_pow_four_le_exp (K := π * η ^ 2) (by positivity) (512 * 3)
  have e4 := eventually_mul_pow_four_le_exp (K := π * η) (by positivity) 8
  have e5 := eventually_mul_pow_four_le_exp (K := π) hpi T₁
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    ((((((eventually_ge_atTop (1 : ℝ)).and e1).and e2).and e3).and e4).and e5)
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨⟨⟨⟨⟨hL1, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hL₀ L hL
  have hTeq : 2 * π * Real.exp (2 * (L - η / 8)) = landauHeight η L := rfl
  have hT0 : 0 ≤ landauHeight η L := (landauHeight_pos η L).le
  -- the net is the set of all distinct zeros of height `≤ T`, at scale `δ = 0`
  classical
  set T := landauHeight η L with hTdef
  set S : Finset ℂ := (lowZeros_finite T).toFinset with hSdef
  have hS : ∀ s ∈ S, s ∈ zetaZeroConfig.carrier := fun s hs =>
    ((lowZeros_finite T).mem_toFinset.mp hs).1
  have hmemS : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ landauHeight η L → ρ ∈ S :=
    fun ρ hρ hρT => (lowZeros_finite T).mem_toFinset.mpr ⟨hρ, hρT⟩
  have hnet : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ landauHeight η L →
      ∃ s ∈ S, ‖ρ - s‖ ≤ 0 := fun ρ hρ hρT => ⟨ρ, hmemS ρ hρ hρT, by simp⟩
  obtain ⟨V, hVfin, hdim, hV, hblind, hW⟩ := nearRadical_at_level_of_net (δ := 0) hη0 hη1 hL1
    hA₀ hloc hCR hcount (sharpCount_cond1 hL1 hCR (Nat.cast_nonneg _) h1)
    (sharpCount_cond2 hL1 hA₀ h2) (sharpCount_cond3 hL1 h3) (sharpCount_cond4 hL1 h4)
    (sharpCount_cond5 hL1 hη1 (by linarith) h5) le_rfl (by simp) S hS hnet
  rw [hTeq] at hdim
  have hcard : (S.card : ℝ) ≤ 2 * (zetaZeroConfig.Nd 0 T : ℝ) + c₀ := by
    have h := hlow T hT0
    rw [Set.ncard_eq_toFinset_card _ (lowZeros_finite T)] at h
    exact_mod_cast h
  refine ⟨V, ⟨fun f hf => hV f hf, fun f hf => ?_⟩, by linarith,
    fun f hf ρ hρ hρT => hblind f hf ρ (hmemS ρ hρ hρT)⟩
  have h := hW f hf
  rw [zero_mul, add_zero] at h
  exact h

/-- **The genus function reads the distinct zeros.** For every `0 < η ≤ 1` and all large `L`,
`g(L, ε_η(L)) ≥ (2 − η)e^{2L} + 2(N(0,T) − N_d(0,T))` with `T = 2πe^{2(L − η/8)}`: each multiple
zero below the Landau height adds its excess multiplicity, twice, to the near radical. -/
theorem genusFunction_ge_distinct {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      (2 - η) * Real.exp (2 * L) +
        2 * ((zetaZeroConfig.N 0 (landauHeight η L) : ℝ) - zetaZeroConfig.Nd 0 (landauHeight η L)) ≤
        (genusFunction L (naturalThreshold η L) : ℝ) := by
  obtain ⟨L₀, hL₀⟩ := exists_nearRadical_blind hη0 hη1
  refine ⟨max L₀ 0, fun L hL => ?_⟩
  obtain ⟨V, hnear, hdim, -⟩ := hL₀ L (le_trans (le_max_left _ _) hL)
  have hle := finrank_le_genusFunction (le_trans (le_max_right _ _) hL)
    (naturalThreshold_pos η L).le hnear
  have hle' : (Module.finrank ℂ V : ℝ) ≤ genusFunction L (naturalThreshold η L) := by
    exact_mod_cast hle
  linarith

/-- `netScale η L · L ≤ 1` once `100(1 + L)⁴ ≤ η² e^{2L}`. -/
theorem netScale_mul_le_one {η L : ℝ} (hL : 1 ≤ L)
    (h : 100 * (1 + L) ^ 4 ≤ η ^ 2 * Real.exp (2 * L)) : netScale η L * L ≤ 1 := by
  unfold netScale
  have hG : L ≤ η ^ 2 * Real.exp (2 * L) / (100 * L) := by
    rw [le_div_iff₀ (by positivity)]
    have hL2 : L ^ 2 ≤ (1 + L) ^ 4 := by
      calc L ^ 2 ≤ (1 + L) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
        _ ≤ (1 + L) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
    nlinarith
  have hexp : L ≤ Real.exp (η ^ 2 * Real.exp (2 * L) / (100 * L)) := by
    have := Real.add_one_le_exp (η ^ 2 * Real.exp (2 * L) / (100 * L))
    linarith
  rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
  exact hexp

/-- `netScale η L · Q(L) e^{9L} ≤ ε_η(L)` once `(2370816000 A₀ + 1350)(1 + L)⁶ ≤ η² e^{2L}`. -/
theorem netScale_mul_netPoly_le {η L A₀ : ℝ} (hL : 1 ≤ L) (hA₀ : 1 ≤ A₀)
    (h : (2370816000 * A₀ + 1350) * (1 + L) ^ 6 ≤ η ^ 2 * Real.exp (2 * L)) :
    netScale η L * (netPoly A₀ L * Real.exp (9 * L)) ≤ naturalThreshold η L := by
  have hA0 : 0 ≤ A₀ := by linarith
  have hL0 : L ≠ 0 := ne_of_gt (by linarith)
  have hQpos : 0 < netPoly A₀ L := by unfold netPoly; positivity
  unfold netScale naturalThreshold
  rw [show Real.exp (-(η ^ 2 * Real.exp (2 * L) / (100 * L))) *
      (netPoly A₀ L * Real.exp (9 * L)) =
      Real.exp (-(η ^ 2 * Real.exp (2 * L) / (100 * L)) + Real.log (netPoly A₀ L) + 9 * L) by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hQpos, mul_assoc]]
  apply Real.exp_le_exp.mpr
  have hlogQ : Real.log (netPoly A₀ L) ≤ netPoly A₀ L := by
    have := Real.log_le_sub_one_of_pos hQpos; linarith
  -- `150 L (Q + 9L) ≤ η² e^{2L}`
  have hpow : L ^ 5 * (3 + 2 * L) ≤ 3 * (1 + L) ^ 6 := by
    have h1 : L ^ 5 ≤ (1 + L) ^ 5 := pow_le_pow_left₀ (by linarith) (by linarith) 5
    have h2 : 3 + 2 * L ≤ 3 * (1 + L) := by linarith
    have h3 : 0 ≤ (1 + L) ^ 5 := by positivity
    calc L ^ 5 * (3 + 2 * L) ≤ (1 + L) ^ 5 * (3 * (1 + L)) :=
          mul_le_mul h1 h2 (by positivity) h3
      _ = 3 * (1 + L) ^ 6 := by ring
  have hL2 : L ^ 2 ≤ (1 + L) ^ 6 := by
    calc L ^ 2 ≤ (1 + L) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
      _ ≤ (1 + L) ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hkey : 150 * L * (netPoly A₀ L + 9 * L) ≤ η ^ 2 * Real.exp (2 * L) := by
    have e : 150 * L * (netPoly A₀ L + 9 * L) =
        790272000 * A₀ * (L ^ 5 * (3 + 2 * L)) + 1350 * L ^ 2 := by unfold netPoly; ring
    rw [e]
    have h1 : 790272000 * A₀ * (L ^ 5 * (3 + 2 * L)) ≤ 790272000 * A₀ * (3 * (1 + L) ^ 6) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    have h2 : 1350 * L ^ 2 ≤ 1350 * (1 + L) ^ 6 := mul_le_mul_of_nonneg_left hL2 (by norm_num)
    linarith
  have hdiv : netPoly A₀ L + 9 * L ≤ η ^ 2 * Real.exp (2 * L) / (150 * L) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have e1 : η ^ 2 * Real.exp (2 * L) / (100 * L) =
      3 * (η ^ 2 * Real.exp (2 * L) / (300 * L)) := by field_simp; ring
  have e2 : η ^ 2 * Real.exp (2 * L) / (150 * L) =
      2 * (η ^ 2 * Real.exp (2 * L) / (300 * L)) := by field_simp; ring
  linarith

/-- **The genus function reads the resolved zeros.** For every `0 < η ≤ 1` and all large `L`, every
finite set `S` of zeros within `netScale η L = exp(−η²e^{2L}/(100L))` of every zero of height
`≤ T = 2πe^{2(L − η/8)}` satisfies `g(L, 2ε_η(L)) ≥ (2 − η)e^{2L} + 2N(0,T) − #S`: the near radical
spends one dimension per *resolved* zero, not per zero. -/
theorem genusFunction_ge_of_net {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ S : Finset ℂ, (∀ s ∈ S, s ∈ zetaZeroConfig.carrier) →
      (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ landauHeight η L →
        ∃ s ∈ S, ‖ρ - s‖ ≤ netScale η L) →
      (2 - η) * Real.exp (2 * L) + 2 * (zetaZeroConfig.N 0 (landauHeight η L) : ℝ) - S.card ≤
        (genusFunction L (2 * naturalThreshold η L) : ℝ) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  obtain ⟨CR, T₁, hCR, hT₁, hcount⟩ := zeroCount_upper
  have hpi := Real.pi_pos
  have e1 := eventually_mul_pow_four_le_exp (K := η / 4) (by positivity) (3 + 0 + 8 * CR)
  have e2 := eventually_mul_pow_four_le_exp (K := η ^ 2) (by positivity)
    (1000 * (4800 * A₀ + 12))
  have e3 := eventually_mul_pow_four_le_exp (K := π * η ^ 2) (by positivity) (512 * 3)
  have e4 := eventually_mul_pow_four_le_exp (K := π * η) (by positivity) 8
  have e5 := eventually_mul_pow_four_le_exp (K := π) hpi T₁
  have e6 := eventually_mul_pow_four_le_exp (K := η ^ 2) (by positivity) 100
  have e7 := eventually_mul_pow_le_exp (K := η ^ 2) (by positivity)
    (2370816000 * A₀ + 1350) 6
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    ((((((((eventually_ge_atTop (1 : ℝ)).and e1).and e2).and e3).and e4).and e5).and e6).and e7)
  refine ⟨L₀, fun L hL S hS hnet => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨hL1, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hL₀ L hL
  obtain ⟨V, hVfin, hdim, hV, -, hW⟩ := nearRadical_at_level_of_net (δ := netScale η L) (c₀ := 0)
    hη0 hη1 hL1 hA₀ hloc hCR hcount
    (by have := sharpCount_cond1 (c := 0) hL1 hCR le_rfl h1; simpa using this)
    (sharpCount_cond2 hL1 hA₀ h2)
    (sharpCount_cond3 hL1 h3) (sharpCount_cond4 hL1 h4)
    (sharpCount_cond5 hL1 hη1 (by linarith) h5) (netScale_pos η L).le
    (netScale_mul_le_one hL1 h6) S hS hnet
  have hTeq : 2 * π * Real.exp (2 * (L - η / 8)) = landauHeight η L := rfl
  rw [hTeq] at hdim
  have hnear : IsNearRadical L (2 * naturalThreshold η L) V := by
    refine ⟨fun f hf => hV f hf, fun f hf => ?_⟩
    refine (hW f hf).trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => sq_nonneg _))
    have := netScale_mul_netPoly_le hL1 hA₀ h7
    unfold naturalThreshold at this ⊢
    linarith
  have hle := finrank_le_genusFunction (by linarith)
    (mul_nonneg two_pos.le (naturalThreshold_pos η L).le) hnear
  have hle' : (Module.finrank ℂ V : ℝ) ≤ genusFunction L (2 * naturalThreshold η L) := by
    exact_mod_cast hle
  push_cast at hdim
  linarith

/-! ### Reparametrization by the height -/

/-- The level at which the Landau height equals `T`: `L = η/8 + ½ log(T/2π)`. -/
def levelOf (η T : ℝ) : ℝ := η / 8 + Real.log (T / (2 * π)) / 2

theorem landauHeight_levelOf {η T : ℝ} (hT : 0 < T) : landauHeight η (levelOf η T) = T := by
  unfold landauHeight levelOf
  rw [show 2 * (η / 8 + Real.log (T / (2 * π)) / 2 - η / 8) = Real.log (T / (2 * π)) by ring,
    Real.exp_log (by positivity)]
  field_simp

theorem le_levelOf {η L₀ T : ℝ} (hT : landauHeight η L₀ ≤ T) : L₀ ≤ levelOf η T := by
  unfold landauHeight at hT
  unfold levelOf
  have h1 : Real.exp (2 * (L₀ - η / 8)) ≤ T / (2 * π) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h2 := Real.log_le_log (Real.exp_pos _) h1
  rw [Real.log_exp] at h2
  linarith

theorem exp_two_mul_levelOf {η T : ℝ} (hT : 0 < T) :
    Real.exp (2 * levelOf η T) = Real.exp (η / 4) * (T / (2 * π)) := by
  unfold levelOf
  rw [show 2 * (η / 8 + Real.log (T / (2 * π)) / 2) = η / 4 + Real.log (T / (2 * π)) by ring,
    Real.exp_add, Real.exp_log (by positivity)]

/-- `e^{η/4} ≤ 2` for `η ≤ 1`, since `1/4 ≤ log 2`. -/
theorem exp_quarter_le_two {η : ℝ} (hη1 : η ≤ 1) : Real.exp (η / 4) ≤ 2 := by
  have hlog2 := Real.log_two_gt_d9
  calc Real.exp (η / 4) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
    _ = 2 := Real.exp_log two_pos

/-- `η e^{2L} ≤ η T` at the level `L` of height `T`, for `0 < η ≤ 1`. -/
theorem mul_exp_two_mul_levelOf_le {η T : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (hT : 0 < T) :
    η * Real.exp (2 * levelOf η T) ≤ η * T := by
  rw [exp_two_mul_levelOf hT]
  have h2 := exp_quarter_le_two hη1
  have hpi := Real.pi_gt_three
  have : Real.exp (η / 4) * (T / (2 * π)) ≤ T := by
    have hT2 : T / (2 * π) ≤ T / 6 :=
      div_le_div_of_nonneg_left hT.le (by norm_num) (by linarith)
    calc Real.exp (η / 4) * (T / (2 * π)) ≤ 2 * (T / 6) :=
          mul_le_mul h2 hT2 (by positivity) (by norm_num)
      _ ≤ T := by linarith
  exact mul_le_mul_of_nonneg_left this hη0.le

/-! ### The implications of the genus law -/

/-- **The genus law bounds the multiplicity excess.** If `g(L, ε_η(L)) ≤ (2 + η)e^{2L}` for all
large `L`, then `N(0,T) − N_d(0,T) ≤ ηT` for all large `T`. -/
theorem multiplicity_excess_le_of_genus_law {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hlaw : ∀ᶠ L : ℝ in atTop,
      (genusFunction L (naturalThreshold η L) : ℝ) ≤ (2 + η) * Real.exp (2 * L)) :
    ∀ᶠ T : ℝ in atTop, (zetaZeroConfig.N 0 T : ℝ) - zetaZeroConfig.Nd 0 T ≤ η * T := by
  obtain ⟨L₀, hL₀⟩ := genusFunction_ge_distinct hη0 hη1
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hlaw
  filter_upwards [eventually_ge_atTop (max (landauHeight η (max L₀ L₁)) 1)] with T hT
  have hTpos : 0 < T := by linarith [le_trans (le_max_right _ _) hT]
  have hL : max L₀ L₁ ≤ levelOf η T := le_levelOf (le_trans (le_max_left _ _) hT)
  have hA := hL₀ _ (le_trans (le_max_left _ _) hL)
  have hB := hL₁ _ (le_trans (le_max_right _ _) hL)
  rw [landauHeight_levelOf hTpos] at hA
  have := mul_exp_two_mul_levelOf_le hη0 hη1 hTpos
  linarith

/-- **The genus law makes almost all zeros simple.** If `g(L, ε_η(L)) ≤ (2 + η)e^{2L}` for all
large `L`, then `N(0,T) − N^s(0,T) ≤ 2ηT` for all large `T`: all but `2ηT` of the zeros of `ζ` up
to height `T`, counted with multiplicity, are simple. -/
theorem nonsimple_le_of_genus_law {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hlaw : ∀ᶠ L : ℝ in atTop,
      (genusFunction L (naturalThreshold η L) : ℝ) ≤ (2 + η) * Real.exp (2 * L)) :
    ∀ᶠ T : ℝ in atTop, (zetaZeroConfig.N 0 T : ℝ) - zetaZeroConfig.Ns 0 T ≤ 2 * η * T := by
  filter_upwards [multiplicity_excess_le_of_genus_law hη0 hη1 hlaw] with T hT
  have h := two_mul_Nd_le_N_add_Ns zetaZeroConfig 0 T
  have h' : 2 * (zetaZeroConfig.Nd 0 T : ℝ) ≤ zetaZeroConfig.N 0 T + zetaZeroConfig.Ns 0 T := by
    exact_mod_cast h
  linarith

/-- The genus law of `ℤ`: `g(L, ε_η(L)) ≤ (2 + η)e^{2L}` for every `0 < η ≤ 1` and all large `L`,
the upper Landau–Widom half asked of the near radical. -/
def GenusLaw : Prop :=
  ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ᶠ L : ℝ in atTop,
    (genusFunction L (naturalThreshold η L) : ℝ) ≤ (2 + η) * Real.exp (2 * L)

/-- Under the genus law, `N(0,T) − N^s(0,T) = o(T)`. -/
theorem nonsimple_isLittleO_of_genusLaw (hlaw : GenusLaw) :
    ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop,
      (zetaZeroConfig.N 0 T : ℝ) - zetaZeroConfig.Ns 0 T ≤ η * T := by
  intro η hη
  have hη' : 0 < min η 1 / 2 := by positivity
  have hη1 : min η 1 / 2 ≤ 1 := by
    have := min_le_right η 1; linarith
  filter_upwards [nonsimple_le_of_genus_law hη' hη1 (hlaw _ hη' hη1),
    eventually_ge_atTop (0 : ℝ)] with T hT hT0
  have : 2 * (min η 1 / 2) * T ≤ η * T := by
    have := min_le_left η 1
    nlinarith
  linarith

/-- Eventually `T ≤ N(0,T)`: the cumulative zero count grows like `T log T`. -/
theorem eventually_le_zetaZeroCount : ∀ᶠ T : ℝ in atTop, T ≤ (zetaZeroConfig.N 0 T : ℝ) := by
  obtain ⟨C, T₁, hC0, hT₁, hlow⟩ := zeroCount_lower
  have hlim : Tendsto (fun T : ℝ => Real.log T ^ 2 / (1 * T + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hsmall : ∀ᶠ T : ℝ in atTop, Real.log T ^ 2 / (1 * T + 0) ≤ 1 / (8 * (C + 1)) :=
    hlim.eventually (ge_mem_nhds (by positivity))
  have hpi := Real.pi_gt_three
  filter_upwards [eventually_ge_atTop T₁, eventually_ge_atTop (2 * π * Real.exp (2 + 2 * π)),
    hsmall, eventually_ge_atTop (1 : ℝ)] with T hT hTbig hlog hT1
  have hTpos : 0 < T := by linarith
  have h1 := hlow T hT
  -- `C log²T ≤ T/8`
  have hlog' : C * Real.log T ^ 2 ≤ T / 8 := by
    rw [one_mul, add_zero, div_le_iff₀ hTpos] at hlog
    have : C * Real.log T ^ 2 ≤ C * (1 / (8 * (C + 1)) * T) :=
      mul_le_mul_of_nonneg_left hlog hC0
    have hCC : C * (1 / (8 * (C + 1)) * T) ≤ T / 8 := by
      rw [show C * (1 / (8 * (C + 1)) * T) = T / 8 * (C / (C + 1)) by field_simp]
      have : C / (C + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      nlinarith
    linarith
  -- `zeroCountMain T ≥ (T/2π)(2π + 1) ≥ T + T/8`
  have hmain : T + T / 8 ≤ zeroCountMain T := by
    unfold zeroCountMain
    have hdiv : Real.exp (2 + 2 * π) ≤ T / (2 * π) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hlogT : 2 + 2 * π ≤ Real.log (T / (2 * π)) := by
      rw [← Real.log_exp (2 + 2 * π)]
      exact Real.log_le_log (Real.exp_pos _) hdiv
    have hTpi : 0 ≤ T / (2 * π) := by positivity
    have : T / (2 * π) * (2 * π + 1) ≤ T / (2 * π) * (Real.log (T / (2 * π)) - 1) := by
      apply mul_le_mul_of_nonneg_left _ hTpi; linarith
    have e : T / (2 * π) * (2 * π + 1) = T + T / (2 * π) := by field_simp
    have h8 : T / 8 ≤ T / (2 * π) :=
      div_le_div_of_nonneg_left hTpos.le (by positivity) (by linarith [Real.pi_le_four])
    linarith
  linarith

/-- **Under the genus law the proportion of simple zeros tends to `1`.** -/
theorem tendsto_simple_ratio_of_genusLaw (hlaw : GenusLaw) :
    Tendsto (fun T : ℝ => (zetaZeroConfig.Ns 0 T : ℝ) / zetaZeroConfig.N 0 T) atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    set η : ℝ := (1 - a) / 2 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    filter_upwards [nonsimple_isLittleO_of_genusLaw hlaw η hη0, eventually_le_zetaZeroCount,
      eventually_ge_atTop (1 : ℝ)] with T hT hN hT1
    have hNpos : (0 : ℝ) < zetaZeroConfig.N 0 T := by linarith
    rw [lt_div_iff₀ hNpos]
    -- `a N < N^s` since `N − N^s ≤ ηT ≤ ηN` and `η < 1 − a`
    have : η * T ≤ η * zetaZeroConfig.N 0 T := mul_le_mul_of_nonneg_left hN hη0.le
    have ha' : a < 1 - η := by rw [hη]; linarith
    nlinarith [mul_pos (sub_pos.mpr ha') hNpos]
  · intro a ha
    filter_upwards [eventually_le_zetaZeroCount, eventually_ge_atTop (1 : ℝ)] with T hN hT1
    have hNpos : (0 : ℝ) < zetaZeroConfig.N 0 T := by linarith
    rw [div_lt_iff₀ hNpos]
    have h := (zetaZeroConfig.trivial_chain 0 T)
    have hNs : (zetaZeroConfig.Ns 0 T : ℝ) ≤ zetaZeroConfig.N 0 T := by
      exact_mod_cast h.2.2.2.2.1.trans h.2.2.2.2.2
    nlinarith

/-! ### Resolution of the zeros under the genus law -/

/-- The resolution scale at height `T`: `exp(−η² T/(20 log T))`. -/
def resolutionScale (η T : ℝ) : ℝ := Real.exp (-(η ^ 2 * T / (20 * Real.log T)))

/-- `2 ε_{2η}(L) ≤ ε_η(L)` once `70(1 + L) ≤ η² e^{2L}`. -/
theorem two_mul_naturalThreshold_two_mul_le {η L : ℝ} (hL : 1 ≤ L)
    (h : 70 * (1 + L) ≤ η ^ 2 * Real.exp (2 * L)) :
    2 * naturalThreshold (2 * η) L ≤ naturalThreshold η L := by
  unfold naturalThreshold
  have h2 : (2 : ℝ) * Real.exp (-((2 * η) ^ 2 * Real.exp (2 * L) / (300 * L))) =
      Real.exp (Real.log 2 + -((2 * η) ^ 2 * Real.exp (2 * L) / (300 * L))) := by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
  rw [h2]
  apply Real.exp_le_exp.mpr
  have hlog2 : Real.log 2 ≤ 7 / 10 := by
    have := Real.log_two_lt_d9; linarith
  have hL0 : 0 < L := by linarith
  have e : (2 * η) ^ 2 * Real.exp (2 * L) / (300 * L) =
      4 * (η ^ 2 * Real.exp (2 * L) / (300 * L)) := by ring
  rw [e]
  have : 7 / 10 ≤ 3 * (η ^ 2 * Real.exp (2 * L) / (300 * L)) := by
    rw [show 3 * (η ^ 2 * Real.exp (2 * L) / (300 * L)) =
      η ^ 2 * Real.exp (2 * L) / (100 * L) by field_simp; ring, le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- At the level `L` of height `T` for the parameter `2η`, `resolutionScale η T ≤ netScale (2η) L`
once `T ≥ e⁵`. -/
theorem resolutionScale_le_netScale {η T : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hT : Real.exp 5 ≤ T) :
    resolutionScale η T ≤ netScale (2 * η) (levelOf (2 * η) T) := by
  unfold resolutionScale netScale
  apply Real.exp_le_exp.mpr
  rw [neg_le_neg_iff]
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hT
  have hlogT : 5 ≤ Real.log T := by
    rw [← Real.log_exp 5]; exact Real.log_le_log (Real.exp_pos _) hT
  have hE : Real.exp (2 * levelOf (2 * η) T) = Real.exp (η / 2) * (T / (2 * π)) := by
    rw [exp_two_mul_levelOf hTpos]; congr 2; ring
  have hpi := Real.pi_gt_three
  have hlog2pi : Real.log (2 * π) ≤ 2 := log_two_pi_lt_two.le
  have hlogdiv : Real.log (T / (2 * π)) = Real.log T - Real.log (2 * π) :=
    Real.log_div hTpos.ne' (by positivity)
  have hLge : Real.log T / 2 - 1 ≤ levelOf (2 * η) T := by
    unfold levelOf; rw [hlogdiv]; linarith
  have hLpos : 0 < levelOf (2 * η) T := by linarith
  have hexp : Real.exp (η / 2) ≤ 2 := by
    have hlog2 := Real.log_two_gt_d9
    calc Real.exp (η / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
      _ = 2 := Real.exp_log two_pos
  have hlogpos : 0 < 20 * Real.log T := by linarith
  set L := levelOf (2 * η) T with hLdef
  rw [hE, show (2 * η) ^ 2 * (Real.exp (η / 2) * (T / (2 * π))) / (100 * L) =
      η ^ 2 * T * (Real.exp (η / 2) / (50 * π * L)) by field_simp; ring,
    show η ^ 2 * T / (20 * Real.log T) = η ^ 2 * T * (1 / (20 * Real.log T)) by ring]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_le_div_iff₀ (by positivity) hlogpos, one_mul]
  -- `e^{η/2} · 20 log T ≤ 50 π L`, from `e^{η/2} ≤ 2`, `π > 3`, `L ≥ ½ log T − 1`, `log T ≥ 5`
  have h1 : Real.exp (η / 2) * (20 * Real.log T) ≤ 2 * (20 * Real.log T) :=
    mul_le_mul_of_nonneg_right hexp hlogpos.le
  have h2 : 150 * L ≤ 50 * π * L := mul_le_mul_of_nonneg_right (by linarith) hLpos.le
  linarith

/-- **The genus law resolves the zeros.** If `g(L, ε_η(L)) ≤ (2 + η)e^{2L}` for all large `L`
(`0 < η ≤ 1/2`), then for all large `T`, every finite set `S` of zeros within
`exp(−η²T/(20 log T))` of every zero of height `≤ T` has at least `2N(0,T) − ηT` points: all but
`o(T)` zeros of height `≤ T` are simple and isolated at the scale `exp(−η²T/(20 log T))`. -/
theorem cover_deficiency_le_of_genus_law {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1 / 2)
    (hlaw : ∀ᶠ L : ℝ in atTop,
      (genusFunction L (naturalThreshold η L) : ℝ) ≤ (2 + η) * Real.exp (2 * L)) :
    ∀ᶠ T : ℝ in atTop, ∀ S : Finset ℂ, (∀ s ∈ S, s ∈ zetaZeroConfig.carrier) →
      (∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ T → ∃ s ∈ S, ‖ρ - s‖ ≤ resolutionScale η T) →
      2 * (zetaZeroConfig.N 0 T : ℝ) - η * T ≤ S.card := by
  have h2η0 : 0 < 2 * η := by linarith
  have h2η1 : 2 * η ≤ 1 := by linarith
  obtain ⟨L₀, hL₀⟩ := genusFunction_ge_of_net h2η0 h2η1
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.mp hlaw
  obtain ⟨L₂, hL₂⟩ := eventually_atTop.mp
    (eventually_mul_pow_le_exp (K := η ^ 2) (by positivity) 70 1)
  filter_upwards [eventually_ge_atTop
    (max (landauHeight (2 * η) (max (max L₀ L₁) (max L₂ 1))) (Real.exp 5))] with T hT S hS hnet
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos 5) (le_trans (le_max_right _ _) hT)
  have hL : max (max L₀ L₁) (max L₂ 1) ≤ levelOf (2 * η) T :=
    le_levelOf (le_trans (le_max_left _ _) hT)
  have hL0 : L₀ ≤ levelOf (2 * η) T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hL1 : L₁ ≤ levelOf (2 * η) T :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hL2 : L₂ ≤ levelOf (2 * η) T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL1' : 1 ≤ levelOf (2 * η) T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hTL : landauHeight (2 * η) (levelOf (2 * η) T) = T := landauHeight_levelOf hTpos
  have hnet' : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im| ≤ landauHeight (2 * η) (levelOf (2 * η) T) →
      ∃ s ∈ S, ‖ρ - s‖ ≤ netScale (2 * η) (levelOf (2 * η) T) := by
    intro ρ hρ hρT
    rw [hTL] at hρT
    obtain ⟨s, hs, h⟩ := hnet ρ hρ hρT
    exact ⟨s, hs, h.trans (resolutionScale_le_netScale hη0 (by linarith)
      (le_trans (le_max_right _ _) hT))⟩
  have hA := hL₀ _ hL0 S hS hnet'
  rw [hTL] at hA
  have hB := hL₁ _ hL1
  have h70 : 70 * (1 + levelOf (2 * η) T) ≤ η ^ 2 * Real.exp (2 * levelOf (2 * η) T) := by
    have := hL₂ _ hL2; simpa using this
  have hthr := two_mul_naturalThreshold_two_mul_le hL1' h70
  have hmono := genusFunction_mono (by linarith : (0 : ℝ) ≤ levelOf (2 * η) T)
    (mul_nonneg two_pos.le (naturalThreshold_pos _ _).le) hthr
  have hmono' : (genusFunction (levelOf (2 * η) T) (2 * naturalThreshold (2 * η)
      (levelOf (2 * η) T)) : ℝ) ≤
      genusFunction (levelOf (2 * η) T) (naturalThreshold η (levelOf (2 * η) T)) := by
    exact_mod_cast hmono
  -- `(2 − 2η)e^{2L} + 2N − #S ≤ g ≤ (2 + η)e^{2L}`, so `2N − #S ≤ 3ηe^{2L} ≤ ηT`
  have hE : Real.exp (2 * levelOf (2 * η) T) = Real.exp (2 * η / 4) * (T / (2 * π)) :=
    exp_two_mul_levelOf hTpos
  have h3 : 3 * η * Real.exp (2 * levelOf (2 * η) T) ≤ η * T := by
    rw [hE]
    have h2 := exp_quarter_le_two (η := 2 * η) h2η1
    have hpi := Real.pi_gt_three
    have hinv : (2 * π)⁻¹ ≤ 1 / 6 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]; norm_num; linarith
    have : 3 * (Real.exp (2 * η / 4) * (T / (2 * π))) ≤ T := by
      rw [div_eq_mul_inv]
      calc 3 * (Real.exp (2 * η / 4) * (T * (2 * π)⁻¹)) ≤ 3 * (2 * (T * (1 / 6))) := by gcongr
        _ = T := by ring
    nlinarith
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_nearRadical_blind
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.genusFunction_ge_of_net
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.multiplicity_excess_le_of_genus_law
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.tendsto_simple_ratio_of_genusLaw
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.cover_deficiency_le_of_genus_law
