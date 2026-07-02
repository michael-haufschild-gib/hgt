/-
# `u₀ ⟂ phiB b` for EVERY `‖b‖ ≥ 4` — the parameterized window capstone

The `b = 4` capstone assembly (`U0PhiFourCapstone`) abstracted over the window branch: the
generic theorem `u0_window_independence_of_transcendental_engine` consumes exactly

* a branch function with its analytic germ on the annulus,
* its transcendence over `ℂ(z)` (the descent theorem), and
* the natural-boundary window engine instance,

and produces the unconditional `NoRelation ℂ(z) (branch) (u₀)`.  Instantiating at
`phiB b` (`U0PhiLargeWindow` engine + `U0PhiLargeDescent` transcendence) yields
**`u0_phiB_independence`: the full algebraic independence of `u₀` and the Böttcher window branch
over `ℂ(z)`, for every parameter `‖b‖ ≥ 4`** — an OPEN SET of parameters, no tower certificate,
no `GBExt` clause, no open input.
-/
import GaloisForLFunctions.U0.U0PhiFourCapstone
import GaloisForLFunctions.U0.U0PhiLargeDescent

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0 U0NaturalBoundary U0PhiFourFarCarrier U0PhiFourDescent U0MeroCarrier
open U0WindowNormalization U0PhiFourCapstone U0PhiLargeWindow U0PhiLargeCarrier U0PhiLargeDescent

namespace U0PhiLargeCapstone

/-- **The generic window capstone assembly.**  Any analytic branch on the window annulus that is
transcendental over `ℂ(z)` and carries the natural-boundary window engine is algebraically
independent of `u₀` over `ℂ(z)`. -/
theorem u0_window_independence_of_transcendental_engine
    (φfun : ℂ → ℂ) (φAn : analyticSubring annW)
    (hφval : ((φAn : analyticSubring annW) : Germ (𝓟 annW) ℂ) = ↑φfun)
    (htransc :
      letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
      letI : Algebra (RatFunc ℂ) (meroField annW) :=
        (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
      Transcendental (RatFunc ℂ)
        (algebraMap (analyticSubring annW) (meroField annW) φAn))
    (engine : ∀ (P' : Polynomial (Polynomial (Polynomial ℂ))) (j₀ : ℕ), 1 ≤ j₀ →
      (∃ z ∈ Metric.ball (0 : ℂ) (21 / 20) ∩ Ext, coeffFun φfun (P'.coeff j₀) z ≠ 0) →
      (∀ z ∈ annW, P'.eval₂ (eval₂RingHom (evalRingHom z) (φfun z)) (u0 z) = 0) → False) :
    letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
    letI : Algebra (RatFunc ℂ) (meroField annW) :=
      (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring annW) (meroField annW) φAn)
      (algebraMap (analyticSubring annW) (meroField annW) (u0AnSub annW_subset_Ext)) := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  letI algR : Algebra (RatFunc ℂ) (meroField annW) :=
    (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
  intro P hrel
  set φM : meroField annW := algebraMap (analyticSubring annW) (meroField annW) φAn with hφM
  set uM : meroField annW :=
    algebraMap (analyticSubring annW) (meroField annW) (u0AnSub annW_subset_Ext) with huM
  set n := P.natDegree with hn
  set N := (Finset.range (n + 1)).sup (fun i => (P.coeff i).natDegree) with hN
  set q : ℕ → ℕ → RatFunc ℂ := fun i j => (P.coeff i).coeff j with hq
  set Wc : ℕ → meroField annW := fun j => ∑ i ∈ Finset.range (n + 1),
    algebraMap (RatFunc ℂ) (meroField annW) (q i j) * φM ^ i with hWc
  have hswap : ∑ j ∈ Finset.range (N + 1), Wc j * uM ^ j = 0 := by
    have h1 : (P.map (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField annW).toRingHom).eval φM
        = ∑ i ∈ Finset.range (n + 1),
            (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField annW) (P.coeff i) * φM ^ i := by
      rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
      rfl
    have h2 : ∀ i ∈ Finset.range (n + 1),
        (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField annW) (P.coeff i)
          = ∑ j ∈ Finset.range (N + 1),
              algebraMap (RatFunc ℂ) (meroField annW) (q i j) * uM ^ j := by
      intro i hi
      rw [aeval_def, Polynomial.eval₂_eq_sum_range]
      refine Finset.sum_subset ?_ ?_
      · have hle : (P.coeff i).natDegree ≤ N :=
          Finset.le_sup (f := fun i => (P.coeff i).natDegree) hi
        intro x hx
        exact Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.succ_le_succ hle))
      · intro j _ hj
        rw [Finset.mem_range, not_lt] at hj
        have hc0 : (P.coeff i).coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hc0, map_zero, zero_mul]
    have hchain : (0 : meroField annW) = ∑ j ∈ Finset.range (N + 1), Wc j * uM ^ j := by
      calc (0 : meroField annW)
          = (P.map (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField annW).toRingHom).eval φM :=
            hrel.symm
        _ = ∑ i ∈ Finset.range (n + 1),
              (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField annW) (P.coeff i) * φM ^ i := h1
        _ = ∑ i ∈ Finset.range (n + 1),
              (∑ j ∈ Finset.range (N + 1),
                algebraMap (RatFunc ℂ) (meroField annW) (q i j) * uM ^ j) * φM ^ i :=
            Finset.sum_congr rfl fun i hi => by rw [h2 i hi]
        _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (N + 1),
              algebraMap (RatFunc ℂ) (meroField annW) (q i j) * uM ^ j * φM ^ i :=
            Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
        _ = ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (n + 1),
              algebraMap (RatFunc ℂ) (meroField annW) (q i j) * uM ^ j * φM ^ i :=
            Finset.sum_comm
        _ = ∑ j ∈ Finset.range (N + 1), Wc j * uM ^ j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [hWc]
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
    exact hchain.symm
  have htransc' := htransc
  rw [transcendental_iff] at htransc'
  by_cases hall : ∀ j ∈ Finset.range (N + 1), 1 ≤ j → Wc j = 0
  · have hW0 : Wc 0 = 0 := by
      have h0 := hswap
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))
        (fun j hj hj0 => by rw [hall j hj (by omega), zero_mul])] at h0
      simpa using h0
    have hWall : ∀ j ∈ Finset.range (N + 1), Wc j = 0 := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with h0 | h1
      · rw [h0]; exact hW0
      · exact hall j hj h1
    have hqzero : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (N + 1), q i j = 0 := by
      intro i hi j hj
      have haev : aeval φM (∑ i' ∈ Finset.range (n + 1), monomial i' (q i' j)) = Wc j := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i' _ => ?_
        rw [aeval_monomial]
      have hRj0 : (∑ i' ∈ Finset.range (n + 1), monomial i' (q i' j))
          = (0 : Polynomial (RatFunc ℂ)) := by
        apply htransc'
        rw [haev]
        exact hWall j hj
      have hco : (∑ i' ∈ Finset.range (n + 1), monomial i' (q i' j)).coeff i = q i j := by
        rw [finsetSum_coeff]
        rw [Finset.sum_congr rfl fun i' _ => coeff_monomial]
        rw [Finset.sum_ite_eq' (Finset.range (n + 1)) i (fun i' => q i' j)]
        rw [if_pos hi]
      rw [← hco, hRj0, coeff_zero]
    apply Polynomial.ext
    intro i
    rw [coeff_zero]
    rcases Nat.lt_or_ge n i with hgt | hle
    · exact coeff_eq_zero_of_natDegree_lt hgt
    · apply Polynomial.ext
      intro j
      rw [coeff_zero]
      rcases Nat.lt_or_ge N j with hgt' | hle'
      · refine coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ?_ hgt')
        exact Finset.le_sup (f := fun i => (P.coeff i).natDegree)
          (Finset.mem_range.mpr (by omega))
      · exact hqzero i (Finset.mem_range.mpr (by omega)) j (Finset.mem_range.mpr (by omega))
  · push Not at hall
    obtain ⟨j₀, hj₀mem, hj₀pos, hWne⟩ := hall
    set D : Polynomial ℂ :=
      ∏ i ∈ Finset.range (n + 1), ∏ j ∈ Finset.range (N + 1), (q i j).denom with hD
    have hDne : D ≠ 0 := by
      rw [hD]
      refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
      exact Finset.prod_ne_zero_iff.mpr fun j _ => (q i j).denom_ne_zero
    have hdvd : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (N + 1), (q i j).denom ∣ D := by
      intro i hi j hj
      rw [hD]
      exact dvd_trans
        (Finset.dvd_prod_of_mem (fun j' => (q i j').denom) hj)
        (Finset.dvd_prod_of_mem (fun i' => ∏ j' ∈ Finset.range (N + 1), (q i' j').denom) hi)
    set q' : ℕ → ℕ → Polynomial ℂ := fun i j => (q i j).num * (D / (q i j).denom) with hq'
    have halgq : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (N + 1),
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (q' i j)
          = algebraMap (Polynomial ℂ) (RatFunc ℂ) D * q i j := by
      intro i hi j hj
      obtain ⟨t, ht⟩ := hdvd i hi j hj
      have hden : (q i j).denom ≠ 0 := (q i j).denom_ne_zero
      have hdiv : D / (q i j).denom = t := by
        rw [ht]
        exact mul_div_cancel_left₀ t hden
      have hdmne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (q i j).denom ≠ 0 := by
        intro h0
        exact hden (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ)
          (h0.trans (map_zero _).symm))
      have hnum : algebraMap (Polynomial ℂ) (RatFunc ℂ) (q i j).num
          = q i j * algebraMap (Polynomial ℂ) (RatFunc ℂ) (q i j).denom :=
        (div_eq_iff hdmne).mp (RatFunc.num_div_denom (q i j))
      simp only [hq']
      rw [hdiv, map_mul, hnum, ht, map_mul]
      ring
    set innerAn : ℕ → analyticSubring annW := fun j =>
      ∑ i ∈ Finset.range (n + 1), polyToAnalytic annW (q' i j) * φAn ^ i with hinnerAn
    have hinner_coe : ∀ j, ((innerAn j : analyticSubring annW) : Germ (𝓟 annW) ℂ)
        = ↑(fun z => ∑ i ∈ Finset.range (n + 1), (q' i j).eval z * φfun z ^ i) := by
      intro j
      simp only [hinnerAn]
      exact sum_mul_pow_coe (fun i => polyToAnalytic annW (q' i j))
        (fun i => fun z => (q' i j).eval z) (fun i _ => rfl) φAn φfun hφval
    have hinner_alg : ∀ j ∈ Finset.range (N + 1),
        algebraMap (analyticSubring annW) (meroField annW) (innerAn j)
          = polyToMero annW D * Wc j := by
      intro j hj
      simp only [hinnerAn]
      rw [map_sum]
      have hterm : ∀ i ∈ Finset.range (n + 1),
          algebraMap (analyticSubring annW) (meroField annW)
              (polyToAnalytic annW (q' i j) * φAn ^ i)
            = polyToMero annW D
              * (algebraMap (RatFunc ℂ) (meroField annW) (q i j) * φM ^ i) := by
        intro i hi
        rw [map_mul, map_pow]
        have hcoeff : algebraMap (analyticSubring annW) (meroField annW)
            (polyToAnalytic annW (q' i j))
              = polyToMero annW D * algebraMap (RatFunc ℂ) (meroField annW) (q i j) := by
          have hpm : algebraMap (analyticSubring annW) (meroField annW)
              (polyToAnalytic annW (q' i j)) = polyToMero annW (q' i j) := rfl
          rw [hpm]
          have h1 : polyToMero annW (q' i j)
              = ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite
                  (algebraMap (Polynomial ℂ) (RatFunc ℂ) (q' i j)) :=
            (ratfuncToMero_algebraMap_polynomial annW isOpen_annW isPreconnected_annW
              annW_nonempty annW_infinite (q' i j)).symm
          rw [h1, halgq i hi j hj, map_mul]
          rw [ratfuncToMero_algebraMap_polynomial]
          rw [RingHom.algebraMap_toAlgebra]
        rw [hcoeff, hφM]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have houter0 : ∑ j ∈ Finset.range (N + 1), innerAn j * (u0AnSub annW_subset_Ext) ^ j
        = (0 : analyticSubring annW) := by
      have halg0 : algebraMap (analyticSubring annW) (meroField annW)
          (∑ j ∈ Finset.range (N + 1), innerAn j * (u0AnSub annW_subset_Ext) ^ j) = 0 := by
        rw [map_sum]
        have hterm : ∀ j ∈ Finset.range (N + 1),
            algebraMap (analyticSubring annW) (meroField annW)
                (innerAn j * (u0AnSub annW_subset_Ext) ^ j)
              = polyToMero annW D * (Wc j * uM ^ j) := by
          intro j hj
          rw [map_mul, map_pow, hinner_alg j hj, huM]
          ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hswap, mul_zero]
      exact (meroField_algebraMap_eq_zero_iff annW isOpen_annW isPreconnected_annW
        annW_nonempty _).mp halg0
    have hpointwise : ∀ z ∈ annW,
        ∑ j ∈ Finset.range (N + 1),
          (∑ i ∈ Finset.range (n + 1), (q' i j).eval z * φfun z ^ i) * u0 z ^ j = 0 :=
      (sum_mul_pow_eq_zero_iff innerAn
        (fun j => fun z => ∑ i ∈ Finset.range (n + 1), (q' i j).eval z * φfun z ^ i)
        (fun j _ => hinner_coe j) (u0AnSub annW_subset_Ext) u0 rfl).mp houter0
    set P' : Polynomial (Polynomial (Polynomial ℂ)) :=
      ∑ j ∈ Finset.range (N + 1),
        monomial j (∑ i ∈ Finset.range (n + 1), monomial i (q' i j)) with hP'
    have hP'coeff : P'.coeff j₀ = ∑ i ∈ Finset.range (n + 1), monomial i (q' i j₀) := by
      rw [hP', finsetSum_coeff]
      rw [Finset.sum_congr rfl fun j _ => coeff_monomial]
      rw [Finset.sum_ite_eq' (Finset.range (N + 1)) j₀
        (fun j => ∑ i ∈ Finset.range (n + 1), monomial i (q' i j))]
      rw [if_pos hj₀mem]
    have hcf : ∀ (p : Polynomial (Polynomial ℂ)) (z : ℂ),
        coeffFun φfun p z = p.eval₂ (evalRingHom z) (φfun z) := fun _ _ => rfl
    have hcfval : ∀ z, coeffFun φfun (P'.coeff j₀) z
        = ∑ i ∈ Finset.range (n + 1), (q' i j₀).eval z * φfun z ^ i := by
      intro z
      rw [hcf, hP'coeff, eval₂_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [eval₂_monomial, coe_evalRingHom]
    have hrel' : ∀ z ∈ annW, P'.eval₂ (eval₂RingHom (evalRingHom z) (φfun z)) (u0 z) = 0 := by
      intro z hz
      rw [hP', eval₂_finsetSum]
      have hterm : ∀ j ∈ Finset.range (N + 1),
          (monomial j (∑ i ∈ Finset.range (n + 1), monomial i (q' i j))).eval₂
              (eval₂RingHom (evalRingHom z) (φfun z)) (u0 z)
            = (∑ i ∈ Finset.range (n + 1), (q' i j).eval z * φfun z ^ i) * u0 z ^ j := by
        intro j _
        rw [eval₂_monomial]
        congr 1
        rw [coe_eval₂RingHom, eval₂_finsetSum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eval₂_monomial, coe_evalRingHom]
      rw [Finset.sum_congr rfl hterm]
      exact hpointwise z hz
    have hwitness : ∃ z ∈ Metric.ball (0 : ℂ) (21 / 20) ∩ Ext,
        coeffFun φfun (P'.coeff j₀) z ≠ 0 := by
      by_contra hno
      push Not at hno
      have hin0 : innerAn j₀ = 0 := by
        simp only [hinnerAn]
        refine (sum_mul_pow_eq_zero_iff (fun i => polyToAnalytic annW (q' i j₀))
          (fun i => fun z => (q' i j₀).eval z) (fun i _ => rfl) φAn φfun hφval).mpr ?_
        intro z hz
        have := hno z hz
        rw [hcfval z] at this
        exact this
      have h1 := hinner_alg j₀ hj₀mem
      rw [hin0, map_zero] at h1
      have hDm : polyToMero annW D ≠ 0 := by
        intro h0
        exact hDne (polyToMero_injective annW isOpen_annW isPreconnected_annW annW_nonempty
          annW_infinite (h0.trans (map_zero _).symm))
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact hDm h
      · exact hWne h
    obtain ⟨z₀, hz₀, hcw⟩ := hwitness
    exact (engine P' j₀ hj₀pos ⟨z₀, hz₀, hcw⟩ hrel').elim

/-- **`u₀ ⟂ phiB b` — UNCONDITIONAL algebraic independence for EVERY `‖b‖ ≥ 4`.**  The window
capstone at an OPEN SET of parameters: in the meromorphic field of the window annulus
`{1 < ‖z‖ < 21/20}`, the Böttcher window branch of any parameter `‖b‖ ≥ 4` and the c-velocity
`u₀` satisfy no nonzero bivariate polynomial relation over `ℂ(z)`.  No tower certificate, no
`GBExt` clause, no open input. -/
theorem u0_phiB_independence {b : ℂ} (hb : 4 ≤ ‖b‖) :
    letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
    letI : Algebra (RatFunc ℂ) (meroField annW) :=
      (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring annW) (meroField annW) (phiBAn b hb))
      (algebraMap (analyticSubring annW) (meroField annW) (u0AnSub annW_subset_Ext)) := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  letI : Algebra (RatFunc ℂ) (meroField annW) :=
    (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
  exact u0_window_independence_of_transcendental_engine (phiB b) (phiBAn b hb) rfl
    (phiB_transcendental hb)
    (fun P' j₀ hj₀ hnd hrel => u0_phiB_no_relation_nondegenerate hb P' hj₀ hnd
      isOpen_annW annW_nonempty (fun z hz => hz) hrel)

end U0PhiLargeCapstone
