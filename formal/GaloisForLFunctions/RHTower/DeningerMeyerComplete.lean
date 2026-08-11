import GaloisForLFunctions.RHTower.DeningerCircleCompleteSpace
import GaloisForLFunctions.RHTower.DeningerMeyerSeminorm
import GaloisForLFunctions.RHTower.DeningerCollarExchange

/-!
# Sequential completeness of the Meyer source

A sequence Cauchy for every Meyer seminorm `q_{A,n}` is uniformly Cauchy in every derivative, so it
has a smooth limit; the exponential bounds pass to the limit because each `q_{A,n}` is bounded along
the sequence, and the convergence is in every seminorm.

* `deningerMeyer_uniformCauchy` : the seminorm-Cauchy condition is uniform Cauchy per derivative.
* `deningerExpSchwartz_exists_limit` : **the limit exists in `H_-`.**
-/

namespace RHTower

open Filter Topology GaloisForLFunctions SchwartzMap
open scoped ContDiff

/-- A Meyer-Cauchy sequence is uniformly Cauchy in every derivative. -/
theorem deningerMeyer_uniformCauchy (F : ℕ → DeningerExpSchwartz)
    (hcauchy : ∀ (A : ℝ) (n : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      deningerMeyerSeminormFun A n (F p - F q) < ε) (n : ℕ) :
    UniformCauchySeqOn
      (fun k => iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)))
      atTop Set.univ := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hcauchy 0 n ε hε
  refine ⟨N, fun p hp q hq x _ => ?_⟩
  have hsplit : iteratedFDeriv ℝ n ((((F p - F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
      = iteratedFDeriv ℝ n ((((F p : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
        - iteratedFDeriv ℝ n ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x := by
    have hsub : ((((F p - F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
        = ((((F p : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
          - ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) := rfl
    rw [hsub]
    exact iteratedFDeriv_sub_apply
      ((((F p : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞)).of_le
        (by exact_mod_cast le_top)).contDiffAt
      ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞)).of_le
        (by exact_mod_cast le_top)).contDiffAt
  have hw := deningerMeyerWeight_le 0 n (F p - F q) x
  rw [deningerMeyerWeight, zero_mul, Real.exp_zero, one_mul, hsplit] at hw
  have hlt : ‖iteratedFDeriv ℝ n ((((F p : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
      - iteratedFDeriv ℝ n ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖ < ε :=
    lt_of_le_of_lt hw (hN p hp q hq)
  have hval : iteratedDeriv n ((((F p : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
      - iteratedDeriv n ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
      = (iteratedFDeriv ℝ n ((((F p : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
          - iteratedFDeriv ℝ n ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x)
        (fun _ => 1) := by
    rw [ContinuousMultilinearMap.sub_apply, ← iteratedDeriv_eq_iteratedFDeriv,
      ← iteratedDeriv_eq_iteratedFDeriv]
  rw [dist_eq_norm, hval]
  refine lt_of_le_of_lt ?_ hlt
  have hle := (iteratedFDeriv ℝ n ((((F p : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
      - iteratedFDeriv ℝ n ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x).le_opNorm
      (fun _ : Fin n => (1 : ℝ))
  simpa using hle

/-- **The limit function of a Meyer-Cauchy sequence**, together with its smoothness, its pointwise
description and the exponential bounds inherited from the sequence. -/
theorem deningerMeyer_exists_limitFun (F : ℕ → DeningerExpSchwartz)
    (hcauchy : ∀ (A : ℝ) (n : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      deningerMeyerSeminormFun A n (F p - F q) < ε) :
    ∃ G : ℝ → ℂ, ContDiff ℝ ∞ G
      ∧ (∀ (n : ℕ) (x : ℝ), Filter.Tendsto
          (fun k => iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x)
          atTop (𝓝 (iteratedDeriv n G x))) := by
  classical
  have hpt : ∀ (n : ℕ) (x : ℝ), ∃ y : ℂ, Filter.Tendsto
      (fun k => iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x)
      atTop (𝓝 y) := by
    intro n x
    exact cauchySeq_tendsto_of_complete
      ((deningerMeyer_uniformCauchy F hcauchy n).cauchySeq (Set.mem_univ x))
  choose Gf hGf using hpt
  have hunif : ∀ n : ℕ, TendstoUniformly
      (fun k => iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)))
      (Gf n) atTop := by
    intro n
    rw [← tendstoUniformlyOn_univ]
    exact (deningerMeyer_uniformCauchy F hcauchy n).tendstoUniformlyOn_of_tendsto
      fun x _ => hGf n x
  have hFsmooth : ∀ k, ContDiff ℝ ∞ ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) :=
    fun k => (((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞))
  refine ⟨Gf 0, contDiff_of_tendstoUniformly_iteratedDeriv hFsmooth hunif, fun n x => ?_⟩
  rw [iteratedDeriv_limit hFsmooth hunif n]
  exact hGf n x

/-- **The limit of a Meyer-Cauchy sequence exists in `H_-`.** -/
theorem deningerExpSchwartz_exists_limit (F : ℕ → DeningerExpSchwartz)
    (hcauchy : ∀ (A : ℝ) (n : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      deningerMeyerSeminormFun A n (F p - F q) < ε) :
    ∃ G : DeningerExpSchwartz, ∀ (A : ℝ) (n : ℕ) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ k ≥ N,
      deningerMeyerSeminormFun A n (F k - G) ≤ ε := by
  classical
  obtain ⟨G₀, hsmooth, hconv⟩ := deningerMeyer_exists_limitFun F hcauchy
  -- the norms of the derivatives converge
  have hnormconv : ∀ (n : ℕ) (x : ℝ), Filter.Tendsto
      (fun k => ‖iteratedFDeriv ℝ n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖)
      atTop (𝓝 ‖iteratedFDeriv ℝ n G₀ x‖) := by
    intro n x
    have h := (hconv n x).norm
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv] using h
  -- the exponential bounds pass to the limit
  have hbd : ∀ (A : ℝ) (n : ℕ), ∃ C : ℝ, ∀ x : ℝ,
      Real.exp (A * |x|) * ‖iteratedFDeriv ℝ n G₀ x‖ ≤ C := by
    intro A n
    obtain ⟨N, hN⟩ := hcauchy A n 1 one_pos
    refine ⟨1 + deningerMeyerSeminormFun A n (F N), fun x => ?_⟩
    have hev : ∀ᶠ k in atTop,
        Real.exp (A * |x|)
            * ‖iteratedFDeriv ℝ n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖
          ≤ 1 + deningerMeyerSeminormFun A n (F N) := by
      refine Filter.eventually_atTop.2 ⟨N, fun k hk => ?_⟩
      have hw := deningerMeyerWeight_le A n (F k) x
      rw [deningerMeyerWeight] at hw
      refine le_trans hw ?_
      have hdecomp : F k = (F k - F N) + F N := by abel
      have hsub : deningerMeyerSeminormFun A n (F k)
          ≤ deningerMeyerSeminormFun A n (F k - F N)
            + deningerMeyerSeminormFun A n (F N) := by
        conv_lhs => rw [hdecomp]
        exact deningerMeyerSeminormFun_add_le A n _ _
      have hlt : deningerMeyerSeminormFun A n (F k - F N) < 1 := hN k hk N (le_refl N)
      linarith
    refine le_of_tendsto ?_ hev
    exact (hnormconv n x).const_mul _
  refine ⟨⟨deningerExpSchwartzOfBounds G₀ hsmooth hbd,
    deningerExpSchwartzOfBounds_mem _ _ _⟩, ?_⟩
  intro A n ε hε
  obtain ⟨N, hN⟩ := hcauchy A n (ε / 2) (by linarith)
  refine ⟨N, fun k hk => ?_⟩
  refine deningerMeyerSeminormFun_le fun x => ?_
  rw [deningerMeyerWeight]
  -- pass to the limit in the Cauchy estimate
  have hev : ∀ᶠ q in atTop,
      Real.exp (A * |x|)
          * ‖iteratedFDeriv ℝ n ((((F k - F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖
        ≤ ε / 2 := by
    refine Filter.eventually_atTop.2 ⟨N, fun q hq => ?_⟩
    have hw := deningerMeyerWeight_le A n (F k - F q) x
    rw [deningerMeyerWeight] at hw
    exact le_of_lt (lt_of_le_of_lt hw (hN k hk q hq))
  have hsplitk : ∀ q : ℕ,
      ‖iteratedFDeriv ℝ n ((((F k - F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖
      = ‖iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
          - iteratedDeriv n ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖ := by
    intro q
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    congr 1
    have hsub : ((((F k - F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
        = ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
          - ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) := rfl
    rw [hsub]
    exact iteratedDeriv_sub_apply_real
      ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞)).of_le
        (by exact_mod_cast le_top)).contDiffAt
      ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞)).of_le
        (by exact_mod_cast le_top)).contDiffAt
  have hlim : Filter.Tendsto
      (fun q => Real.exp (A * |x|)
        * ‖iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
            - iteratedDeriv n ((((F q : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖)
      atTop (𝓝 (Real.exp (A * |x|)
        * ‖iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
            - iteratedDeriv n G₀ x‖)) :=
    ((tendsto_const_nhds.sub (hconv n x)).norm).const_mul _
  have hle : Real.exp (A * |x|)
      * ‖iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
          - iteratedDeriv n G₀ x‖ ≤ ε / 2 := by
    refine le_of_tendsto hlim ?_
    refine hev.mono fun q hq => ?_
    rwa [hsplitk q] at hq
  have hfinal : ‖iteratedFDeriv ℝ n
      ((((F k - ⟨deningerExpSchwartzOfBounds G₀ hsmooth hbd,
        deningerExpSchwartzOfBounds_mem _ _ _⟩ : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x‖
      = ‖iteratedDeriv n ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) x
          - iteratedDeriv n G₀ x‖ := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    congr 1
    have hsub : ((((F k - ⟨deningerExpSchwartzOfBounds G₀ hsmooth hbd,
        deningerExpSchwartzOfBounds_mem _ _ _⟩ : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ))
        = ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) - G₀ := rfl
    rw [hsub]
    exact iteratedDeriv_sub_apply_real
      ((((F k : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)).smooth (⊤ : ℕ∞)).of_le
        (by exact_mod_cast le_top)).contDiffAt
      (hsmooth.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [hfinal]
  linarith

end RHTower
