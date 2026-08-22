import GaloisForLFunctions.RHTower.MertensPrimeMeanReader
import GaloisForLFunctions.RHTower.GammaMeixnerAbelCoronaProbe

/-!
# The actual Euler Mertens class is a rank-one shift conormal

On the actual Euler coefficient space `E_actual = ℝ·1 + M_0` the Mertens mean is the canonical
coordinate `q_M` of the one-dimensional quotient line.  This file proves that the prime unit
translation `(S_h b)_p = p^{-h} b_p` sends the *whole* logarithmic Marcinkiewicz layer into the
vanishing-tail layer, so that

```text
q_M ∘ S_h = 0        and        q_M ∘ (I − S_h) = q_M
```

for every `h > 0`: the corona conormal is a cyclic rank-one module for the dual shift action.

* `primeUnitTranslation`, `sum_primeUnitTranslation_dyadic_block_le`,
  `memCriticalSummableLayer_primeUnitTranslation`,
  `memVanishingTailLayer_primeUnitTranslation` — equations (7), (17)--(19);
* `memVanishingTailLayer_primeUnitTranslation_unit` — equation (8);
* `tendsto_mertensPrimeMean_primeUnitTranslation_zero` — equation (9);
* `tendsto_mertensPrimeMean_sourceDefect` — equation (10);
* `abs_le_of_marcinkiewiczLogQuotient_le` — equation (6);
* `mertensCoronaShiftConormal` — the packaged rank-one law;
* `tendsto_gammaShapeAbelFunctional_actual` — equation (13), the Gamma--Meixner Abel realization
  on the whole actual space, built on `RHTower.GammaMeixnerAbelCoronaProbe`;
* `coronaPolarGermJet`, `hasDerivAt_coronaPolarGermJet`, `coronaPolarGermJet_ne_zero` —
  equations (17)--(18) and the nonvanishing (21).

The quotient-line facts (4)--(6) and the Abel limits (11)--(12) are the corpus modules
`RHTower.MertensPrimeMeanReader`, `RHTower.WeightedEulerCoefficientSpaces` and
`RHTower.GammaMeixnerAbelCoronaProbe`.
-/

open Finset Filter Topology

namespace RHTower

noncomputable section

/-- The prime unit translation `(S_h b)_p = p^{-h} b_p`, equation (7)/(16). -/
def primeUnitTranslation (h : ℝ) (b : ℕ → ℝ) : ℕ → ℝ := fun p => (p : ℝ) ^ (-h) * b p

theorem primeUnitTranslation_apply (h : ℝ) (b : ℕ → ℝ) (p : ℕ) :
    primeUnitTranslation h b p = (p : ℝ) ^ (-h) * b p := rfl

/-! ## The dyadic bound for a positively translated Marcinkiewicz field -/

theorem primeLogMass_le_of_marcinkiewicz {b : ℕ → ℝ} {C : ℝ}
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C) {X : ℕ} (hX : 2 ≤ X) :
    primeLogMass b X ≤ C * Real.log X := by
  have hlog : 0 < Real.log X := log_cutoff_pos hX
  have h := hC X hX
  rw [marcinkiewiczLogQuotient, div_le_iff₀ hlog] at h
  exact h

/-- The dyadic block bound: on `2^j ≤ p < 2^{j+1}` the translated prime-log mass is at most
`C (j+1) log 2 · (2^{-h})^j`. -/
theorem sum_primeUnitTranslation_dyadic_block_le {b : ℕ → ℝ} {C h : ℝ} (hh : 0 < h)
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient b X ≤ C) (j N : ℕ) :
    ∑ p ∈ {p ∈ Nat.primesBelow N | Nat.log 2 p = j},
        Real.log p / p * |primeUnitTranslation h b p|
      ≤ C * ((j : ℝ) + 1) * Real.log 2 * ((2 : ℝ) ^ (-h)) ^ j := by
  classical
  set B := {p ∈ Nat.primesBelow N | Nat.log 2 p = j} with hB
  have hmem : ∀ p ∈ B, 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) ∧ p.Prime := by
    intro p hp
    obtain ⟨hpmem, hlog⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, hpp⟩ := Nat.mem_primesBelow.mp hpmem
    refine ⟨?_, ?_, hpp⟩
    · rw [← hlog]
      exact Nat.pow_log_le_self 2 hpp.pos.ne'
    · rw [← hlog]
      exact Nat.lt_pow_succ_log_self one_lt_two p
  have hterm : ∀ p ∈ B, Real.log p / p * |primeUnitTranslation h b p|
      ≤ ((2 : ℝ) ^ (-h)) ^ j * (Real.log p / p * |b p|) := by
    intro p hp
    obtain ⟨hlow, -, hpp⟩ := hmem p hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have h2j : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hcast : ((2 : ℝ) ^ j) ≤ (p : ℝ) := by exact_mod_cast hlow
    have hpow : (p : ℝ) ^ (-h) ≤ ((2 : ℝ) ^ j) ^ (-h) := by
      rw [Real.rpow_neg hp0.le, Real.rpow_neg h2j.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos h2j _) (Real.rpow_le_rpow h2j.le hcast hh.le)
    have hrw : ((2 : ℝ) ^ j) ^ (-h) = ((2 : ℝ) ^ (-h)) ^ j := by
      rw [← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast ((2 : ℝ) ^ (-h)) j, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    rw [hrw] at hpow
    have hmass : (0 : ℝ) ≤ Real.log p / p * |b p| := primeLog_term_nonneg b p
    have habs : |primeUnitTranslation h b p| = (p : ℝ) ^ (-h) * |b p| := by
      rw [primeUnitTranslation, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hp0 _)]
    rw [habs]
    have hlogp : (0 : ℝ) ≤ Real.log p := Real.log_natCast_nonneg p
    calc Real.log p / p * ((p : ℝ) ^ (-h) * |b p|)
        = (p : ℝ) ^ (-h) * (Real.log p / p * |b p|) := by ring
      _ ≤ ((2 : ℝ) ^ (-h)) ^ j * (Real.log p / p * |b p|) :=
          mul_le_mul_of_nonneg_right hpow hmass
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have hsub : B ⊆ (Finset.Icc 1 (2 ^ (j + 1))).filter Nat.Prime := by
    intro p hp
    obtain ⟨-, hup, hpp⟩ := hmem p hp
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hpp.one_lt.le.trans' (by norm_num), by omega⟩, hpp⟩
  have hmassle : ∑ p ∈ B, (Real.log p / p * |b p|) ≤ primeLogMass b (2 ^ (j + 1)) := by
    rw [primeLogMass]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => primeLog_term_nonneg b p
  have hbound : primeLogMass b (2 ^ (j + 1)) ≤ C * ((j : ℝ) + 1) * Real.log 2 := by
    have h2 : 2 ≤ 2 ^ (j + 1) := Nat.le_self_pow (by omega) 2
    have := primeLogMass_le_of_marcinkiewicz hC h2
    have hlogpow : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) = ((j : ℝ) + 1) * Real.log 2 := by
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    rw [hlogpow] at this
    linarith [this]
  have hgeo : (0 : ℝ) ≤ ((2 : ℝ) ^ (-h)) ^ j := by positivity
  nlinarith [hmassle, hbound, hgeo]


/-! ## Equation (19): every positive Euler translation lands in the vanishing-tail layer -/

theorem summable_dyadicShiftWeight {h : ℝ} (hh : 0 < h) :
    Summable (fun j : ℕ => ((j : ℝ) + 1) * ((2 : ℝ) ^ (-h)) ^ j) := by
  have hrpos : (0 : ℝ) < (2 : ℝ) ^ (-h) := Real.rpow_pos_of_pos (by norm_num) _
  have hr : ‖((2 : ℝ) ^ (-h))‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrpos]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have h1 : Summable (fun j : ℕ => (j : ℝ) * ((2 : ℝ) ^ (-h)) ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have h2 : Summable (fun j : ℕ => ((2 : ℝ) ^ (-h)) ^ j) := summable_geometric_of_norm_lt_one hr
  refine (h1.add h2).congr fun j => ?_
  ring

/-- The dyadic constant of the shift bound. -/
def dyadicShiftConstant (h : ℝ) : ℝ := ∑' j : ℕ, ((j : ℝ) + 1) * ((2 : ℝ) ^ (-h)) ^ j

theorem dyadicShiftConstant_nonneg {h : ℝ} (hh : 0 < h) : 0 ≤ dyadicShiftConstant h := by
  refine tsum_nonneg fun j => ?_
  positivity

/-- **Equations (17)--(18).**  A positive translation of a logarithmic Marcinkiewicz field has
absolutely summable prime-log mass. -/
theorem memCriticalSummableLayer_primeUnitTranslation {b : ℕ → ℝ} {h : ℝ} (hh : 0 < h)
    (hb : MemMarcinkiewiczLogLayer b) :
    MemCriticalSummableLayer (primeUnitTranslation h b) := by
  classical
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := by
    have h2 := hC 2 le_rfl
    have hq : 0 ≤ marcinkiewiczLogQuotient b 2 := by
      rw [marcinkiewiczLogQuotient]
      exact div_nonneg (primeLogMass_nonneg b 2) (log_cutoff_pos (le_refl 2)).le
    linarith
  have hsummable := summable_dyadicShiftWeight hh
  refine summable_of_sum_range_le (c := C * Real.log 2 * dyadicShiftConstant h) ?_ ?_
  · intro n
    by_cases hp : n.Prime
    · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime} from hp)]
      exact primeLog_term_nonneg _ n
    · rw [Set.indicator_of_notMem (show n ∉ {p : ℕ | p.Prime} from hp)]
  · intro n
    have hfilter : ∑ i ∈ Finset.range n,
        ({p : ℕ | p.Prime}.indicator fun m => Real.log m / m * |primeUnitTranslation h b m|) i
        = ∑ p ∈ Nat.primesBelow n, Real.log p / p * |primeUnitTranslation h b p| := by
      rw [show Nat.primesBelow n = (Finset.range n).filter Nat.Prime from rfl,
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hp : i.Prime
      · rw [Set.indicator_of_mem (show i ∈ {p : ℕ | p.Prime} from hp), if_pos hp]
      · rw [Set.indicator_of_notMem (show i ∉ {p : ℕ | p.Prime} from hp), if_neg hp]
    rw [hfilter]
    have hmaps : ∀ p ∈ Nat.primesBelow n, Nat.log 2 p ∈ Finset.range (Nat.log 2 n + 1) := by
      intro p hp
      obtain ⟨hpn, -⟩ := Nat.mem_primesBelow.mp hp
      rw [Finset.mem_range]
      have : Nat.log 2 p ≤ Nat.log 2 n := Nat.log_mono_right hpn.le
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun p => Real.log p / p * |primeUnitTranslation h b p|)]
    have hblock : ∀ j ∈ Finset.range (Nat.log 2 n + 1),
        ∑ p ∈ {p ∈ Nat.primesBelow n | Nat.log 2 p = j},
            Real.log p / p * |primeUnitTranslation h b p|
          ≤ C * Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-h)) ^ j) := by
      intro j _
      have := sum_primeUnitTranslation_dyadic_block_le hh hC j n
      calc ∑ p ∈ {p ∈ Nat.primesBelow n | Nat.log 2 p = j},
              Real.log p / p * |primeUnitTranslation h b p|
          ≤ C * ((j : ℝ) + 1) * Real.log 2 * ((2 : ℝ) ^ (-h)) ^ j := this
        _ = C * Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-h)) ^ j) := by ring
    refine le_trans (Finset.sum_le_sum hblock) ?_
    rw [← Finset.mul_sum]
    have hpart : ∑ j ∈ Finset.range (Nat.log 2 n + 1), ((j : ℝ) + 1) * ((2 : ℝ) ^ (-h)) ^ j
        ≤ dyadicShiftConstant h := by
      exact hsummable.sum_le_tsum _ (fun j _ => by positivity)
    have hCl : (0 : ℝ) ≤ C * Real.log 2 := by
      have : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    exact mul_le_mul_of_nonneg_left hpart hCl

/-- **Equation (19).**  Every positive Euler translation maps the logarithmic Marcinkiewicz layer
into the vanishing-tail layer. -/
theorem memVanishingTailLayer_primeUnitTranslation {b : ℕ → ℝ} {h : ℝ} (hh : 0 < h)
    (hb : MemMarcinkiewiczLogLayer b) :
    MemVanishingTailLayer (primeUnitTranslation h b) :=
  memVanishingTailLayer_of_memCriticalSummableLayer
    (memCriticalSummableLayer_primeUnitTranslation hh hb)


/-! ## The actual Euler coefficient space and its conormal -/

/-- The actual Euler coefficient space `E_actual = ℝ·1 + M_0`, equation (2). -/
def MemActualEulerSpace (x : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, MemVanishingTailLayer fun n => x n - c

theorem memActualEulerSpace_unit : MemActualEulerSpace (fun _ => (1 : ℝ)) :=
  ⟨1, by
    have hzero : (fun n : ℕ => (1 : ℝ) - 1) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      ring
    rw [hzero]
    exact memVanishingTailLayer_of_memCriticalSummableLayer
      (memCriticalSummableLayer_of_finite_support ∅ fun n _ => rfl)⟩

/-- **Equation (3).**  Every element of the actual source space lies in the logarithmic
Marcinkiewicz layer. -/
theorem memMarcinkiewiczLogLayer_of_actual {x : ℕ → ℝ} (hx : MemActualEulerSpace x) :
    MemMarcinkiewiczLogLayer x := by
  obtain ⟨c, hc⟩ := hx
  have h1 : MemMarcinkiewiczLogLayer fun n => x n - c :=
    memMarcinkiewiczLogLayer_of_memVanishingTailLayer hc
  have h2 : MemMarcinkiewiczLogLayer fun _ : ℕ => c := by
    have := memMarcinkiewiczLogLayer_smul (b := fun _ : ℕ => (1 : ℝ)) (k := c)
      unitField_memMarcinkiewiczLogLayer
    simpa using this
  have h3 := memMarcinkiewiczLogLayer_add h1 h2
  refine h3.imp fun C hC => ?_
  intro X hX
  have hcongr : (fun n : ℕ => (x n - c) + c) = x := by
    funext n
    ring
  rw [hcongr] at hC
  exact hC X hX

theorem mertensPrimeMean_sub (x y : ℕ → ℝ) (X : ℕ) :
    mertensPrimeMean (fun n => x n - y n) X = mertensPrimeMean x X - mertensPrimeMean y X := by
  rw [mertensPrimeMean, mertensPrimeMean, mertensPrimeMean, ← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Equation (8).**  The positive translation of the actual unit lands in the vanishing-tail
layer. -/
theorem memVanishingTailLayer_primeUnitTranslation_unit {h : ℝ} (hh : 0 < h) :
    MemVanishingTailLayer (primeUnitTranslation h fun _ => (1 : ℝ)) :=
  memVanishingTailLayer_primeUnitTranslation hh unitField_memMarcinkiewiczLogLayer

/-- **Equation (9).**  The Mertens conormal annihilates every positively translated source:
`q_M ∘ S_h = 0`. -/
theorem tendsto_mertensPrimeMean_primeUnitTranslation_zero {x : ℕ → ℝ} {h : ℝ} (hh : 0 < h)
    (hx : MemActualEulerSpace x) :
    Tendsto (mertensPrimeMean (primeUnitTranslation h x)) atTop (nhds 0) :=
  tendsto_mertensPrimeMean_zero_of_vanishingTail
    (memVanishingTailLayer_primeUnitTranslation hh (memMarcinkiewiczLogLayer_of_actual hx))

/-- **Equation (10).**  The complete source defect `D = I − S_h` is detected by the Mertens
conormal with eigenvalue one: `q_M ∘ D = q_M`. -/
theorem tendsto_mertensPrimeMean_sourceDefect {x : ℕ → ℝ} {c h : ℝ} (hh : 0 < h)
    (hc : MemVanishingTailLayer fun n => x n - c) :
    Tendsto (mertensPrimeMean fun n => x n - primeUnitTranslation h x n) atTop (nhds c) := by
  have hx : MemActualEulerSpace x := ⟨c, hc⟩
  have h1 := tendsto_mertensPrimeMean_of_vanishingTail hc
  have h2 := tendsto_mertensPrimeMean_primeUnitTranslation_zero hh hx
  have hsub := h1.sub h2
  rw [sub_zero] at hsub
  exact hsub.congr fun X => (mertensPrimeMean_sub x (primeUnitTranslation h x) X).symm

/-- **Equation (6).**  The conormal is continuous for the Marcinkiewicz seminorm: the constant is
bounded by every uniform bound on the logarithmic quotients. -/
theorem abs_le_of_marcinkiewiczLogQuotient_le {x : ℕ → ℝ} {c C : ℝ}
    (hc : MemVanishingTailLayer fun n => x n - c)
    (hC : ∀ X : ℕ, 2 ≤ X → marcinkiewiczLogQuotient x X ≤ C) : |c| ≤ C := by
  have hlim := (tendsto_mertensPrimeMean_of_vanishingTail hc).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with X hX
  exact le_trans (abs_mertensPrimeMean_le x hX) (hC X hX)

/-- **The rank-one shift-conormal law, equations (5), (9), (10).**  On the actual Euler
coefficient space the Mertens mean reads the unit coefficient, annihilates every positive
translation, and detects the complete translation defect with eigenvalue one. -/
theorem mertensCoronaShiftConormal {x : ℕ → ℝ} {c h : ℝ} (hh : 0 < h)
    (hc : MemVanishingTailLayer fun n => x n - c) :
    Tendsto (mertensPrimeMean x) atTop (nhds c)
      ∧ Tendsto (mertensPrimeMean (primeUnitTranslation h x)) atTop (nhds 0)
      ∧ Tendsto (mertensPrimeMean fun n => x n - primeUnitTranslation h x n) atTop (nhds c) :=
  ⟨tendsto_mertensPrimeMean_of_vanishingTail hc,
    tendsto_mertensPrimeMean_primeUnitTranslation_zero hh ⟨c, hc⟩,
    tendsto_mertensPrimeMean_sourceDefect hh hc⟩


/-! ## Equation (13): the Gamma--Meixner Abel family converges to the conormal -/

theorem gammaShapeAbelFunctional_smul (θ c : ℝ) (b : ℕ → ℝ) :
    gammaShapeAbelFunctional θ (fun n => c * b n) = c * gammaShapeAbelFunctional θ b := by
  rw [gammaShapeAbelFunctional, gammaShapeAbelFunctional]
  rw [show (fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * (c * b n))
      = fun n : ℕ => c * (mertensPrimeWeight n * meixnerShape θ n * b n) from
    funext fun n => by ring]
  rw [tsum_mul_left]
  ring

/-- **Equation (13).**  The Gamma--Meixner Abel family converges pointwise on the whole actual
Euler coefficient space to the Mertens conormal. -/
theorem tendsto_gammaShapeAbelFunctional_actual {x : ℕ → ℝ} {c : ℝ}
    (hc : MemVanishingTailLayer fun n => x n - c) :
    Tendsto (fun θ : ℝ => gammaShapeAbelFunctional θ x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
  obtain ⟨C, hC⟩ := memMarcinkiewiczLogLayer_of_memVanishingTailLayer hc
  have hlim : Tendsto (fun θ : ℝ => c * gammaShapeAbelFunctional θ (fun _ => (1 : ℝ))
      + gammaShapeAbelFunctional θ (fun n => x n - c))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds c) := by
    have h := (tendsto_gammaShapeAbelFunctional_unit.const_mul c).add
      (tendsto_gammaShapeAbelFunctional_vanishingTail hc)
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ
  have hs1 : Summable (fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * (c * 1)) := by
    have h := (summable_gammaShapeTerm_unit hθ0).mul_left c
    refine h.congr fun n => ?_
    ring
  have hs2 : Summable (fun n : ℕ => mertensPrimeWeight n * meixnerShape θ n * (x n - c)) :=
    summable_gammaShapeTerm hθ0 hC
  calc c * gammaShapeAbelFunctional θ (fun _ => (1 : ℝ))
        + gammaShapeAbelFunctional θ (fun n => x n - c)
      = gammaShapeAbelFunctional θ (fun n => c * 1)
        + gammaShapeAbelFunctional θ (fun n => x n - c) := by
        rw [gammaShapeAbelFunctional_smul]
    _ = gammaShapeAbelFunctional θ (fun n => c * 1 + (x n - c)) :=
        (gammaShapeAbelFunctional_add_of_summable hs1 hs2).symm
    _ = gammaShapeAbelFunctional θ x := by
        congr 1
        funext n
        ring

/-! ## Equations (17)--(18) and (21): the polar germ and its factorial jet -/

/-- The polar germ of the conormal class, equation (17). -/
def coronaPolarGerm (c z : ℝ) : ℝ := Real.sqrt 2 * c / z

/-- The `N`-th raw derivative of the polar germ, equation (18). -/
def coronaPolarGermJet (c : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  Real.sqrt 2 * c * (-1) ^ N * (Nat.factorial N : ℝ) / z ^ (N + 1)

theorem coronaPolarGermJet_zero (c : ℝ) : coronaPolarGermJet c 0 = coronaPolarGerm c := by
  funext z
  rw [coronaPolarGermJet, coronaPolarGerm]
  norm_num

/-- **Equation (18).**  Differentiating the polar germ once raises the factorial jet order. -/
theorem hasDerivAt_coronaPolarGermJet (c : ℝ) (N : ℕ) {x₀ : ℝ} (hx : x₀ ≠ 0) :
    HasDerivAt (coronaPolarGermJet c N) (coronaPolarGermJet c (N + 1) x₀) x₀ := by
  have hpow : HasDerivAt (fun z : ℝ => z ^ (N + 1)) (((N : ℝ) + 1) * x₀ ^ N) x₀ := by
    have := hasDerivAt_pow (N + 1) x₀
    simpa using this
  have hne : x₀ ^ (N + 1) ≠ 0 := pow_ne_zero _ hx
  have hdiv := (hasDerivAt_const x₀ (Real.sqrt 2 * c * (-1 : ℝ) ^ N * (Nat.factorial N : ℝ))).div hpow hne
  refine hdiv.congr_deriv ?_
  rw [coronaPolarGermJet]
  have hfact : (Nat.factorial (N + 1) : ℝ) = ((N : ℝ) + 1) * (Nat.factorial N : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfact]
  field_simp
  ring

/-- **Equation (21).**  For a nonzero conormal coefficient the factorial jet is nonzero at every
resolution. -/
theorem coronaPolarGermJet_ne_zero {c : ℝ} (hc : c ≠ 0) (N : ℕ) {x₀ : ℝ} (hx : x₀ ≠ 0) :
    coronaPolarGermJet c N x₀ ≠ 0 := by
  have h2 : Real.sqrt 2 ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    exact ne_of_gt this
  have hfact : ((Nat.factorial N : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  have hsign : ((-1 : ℝ)) ^ N ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  rw [coronaPolarGermJet]
  exact div_ne_zero (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 hc) hsign) hfact) (pow_ne_zero _ hx)

end

end RHTower
