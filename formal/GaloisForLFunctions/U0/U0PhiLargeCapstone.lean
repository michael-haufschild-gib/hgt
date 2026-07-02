/-
# `u₀ ⟂ phiB b` for EVERY `‖b‖ > 2+√2` — the sharp window capstone

The capstone assembly abstracted over BOTH the window branch and its carrier: the generic
theorem `u0_window_independence_of_transcendental_engine` consumes exactly

* a carrier `U` (open, preconnected, nonempty, infinite, inside `u₀`'s domain `Ext`),
* a branch function with its analytic germ on `U`,
* its transcendence over `ℂ(z)` (the descent theorem), and
* the natural-boundary window engine instance on `U`,

and produces the unconditional `NoRelation ℂ(z) (branch) (u₀)`.  Instantiating at the sharp
carrier `annWB b` with `phiB b` (`U0PhiLargeWindow` engine + `U0PhiLargeDescent` transcendence)
yields **`u0_phiB_independence`: the full algebraic independence of `u₀` and the Böttcher window
branch over `ℂ(z)`, for every parameter `‖b‖ > 2+√2`** — the sharp threshold, an OPEN SET of
parameters, no tower certificate, no `GBExt` clause, no open input.
-/
import GaloisForLFunctions.U0.U0PhiFourCapstone
import GaloisForLFunctions.U0.U0PhiLargeDescent

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0 U0NaturalBoundary U0PhiFourFarCarrier U0PhiFourDescent U0MeroCarrier
open U0WindowNormalization U0PhiFourCapstone U0PhiLargeWindow U0PhiLargeCarrier U0PhiLargeDescent

namespace U0PhiLargeCapstone

/-! ## Germ realization of layered sums, on an arbitrary carrier -/

/-- Values of a layered sum `∑ eⱼ·bʲ` of analytic germs on an arbitrary carrier (the generic
form of `U0PhiFourCapstone.sum_mul_pow_coe`). -/
theorem sum_mul_pow_coe_U {U : Set ℂ} {k : ℕ} (e : ℕ → analyticSubring U) (g : ℕ → ℂ → ℂ)
    (hval : ∀ j ∈ Finset.range k, ((e j : analyticSubring U) : Germ (𝓟 U) ℂ) = ↑(g j))
    (b : analyticSubring U) (f : ℂ → ℂ)
    (hb : ((b : analyticSubring U) : Germ (𝓟 U) ℂ) = ↑f) :
    ((∑ j ∈ Finset.range k, e j * b ^ j : analyticSubring U) : Germ (𝓟 U) ℂ)
      = ↑(fun z => ∑ j ∈ Finset.range k, g j z * f z ^ j) := by
  have h1 : ((∑ j ∈ Finset.range k, e j * b ^ j : analyticSubring U) : Germ (𝓟 U) ℂ)
      = ∑ j ∈ Finset.range k,
          ((e j : analyticSubring U) : Germ (𝓟 U) ℂ)
            * (((b : analyticSubring U) : Germ (𝓟 U) ℂ)) ^ j := by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun j _ => by rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have h2 : (fun z => ∑ j ∈ Finset.range k, g j z * f z ^ j)
      = ∑ j ∈ Finset.range k, (g j * f ^ j) := by
    funext z
    rw [Finset.sum_apply]
    rfl
  rw [h1, h2]
  have h3 : ((↑(∑ j ∈ Finset.range k, (g j * f ^ j)) : Germ (𝓟 U) ℂ))
      = ∑ j ∈ Finset.range k, (↑(g j * f ^ j) : Germ (𝓟 U) ℂ) :=
    map_sum (Germ.coeRingHom (𝓟 U)) _ _
  rw [h3]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hval j hj, hb]
  rw [← Germ.coe_pow, ← Germ.coe_mul]

/-- Vanishing bridge on an arbitrary carrier: the layered analytic-germ sum is zero iff its
pointwise realization vanishes on the carrier. -/
theorem sum_mul_pow_eq_zero_iff_U {U : Set ℂ} {k : ℕ} (e : ℕ → analyticSubring U)
    (g : ℕ → ℂ → ℂ)
    (hval : ∀ j ∈ Finset.range k, ((e j : analyticSubring U) : Germ (𝓟 U) ℂ) = ↑(g j))
    (b : analyticSubring U) (f : ℂ → ℂ)
    (hb : ((b : analyticSubring U) : Germ (𝓟 U) ℂ) = ↑f) :
    (∑ j ∈ Finset.range k, e j * b ^ j = (0 : analyticSubring U))
      ↔ ∀ z ∈ U, ∑ j ∈ Finset.range k, g j z * f z ^ j = 0 := by
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero, sum_mul_pow_coe_U e g hval b f hb]
  rw [← Germ.coe_zero, Germ.coe_eq]
  constructor
  · intro h z hz
    exact eventually_principal.mp h z hz
  · intro h
    apply eventually_principal.mpr
    intro z hz
    exact h z hz

/-! ## The generic capstone assembly -/

/-- **The generic window capstone assembly, carrier-parameterized.**  Any analytic branch on a
window carrier that is transcendental over `ℂ(z)` and carries the natural-boundary window
engine is algebraically independent of `u₀` over `ℂ(z)`. -/
theorem u0_window_independence_of_transcendental_engine
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hUinf : U.Infinite) (hUExt : U ⊆ Ext)
    (φfun : ℂ → ℂ) (φAn : analyticSubring U)
    (hφval : ((φAn : analyticSubring U) : Germ (𝓟 U) ℂ) = ↑φfun)
    (htransc :
      letI := isDomain_analyticSubring U hUo hUc hUne
      letI : Algebra (RatFunc ℂ) (meroField U) :=
        (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
      Transcendental (RatFunc ℂ)
        (algebraMap (analyticSubring U) (meroField U) φAn))
    (engine : ∀ (P' : Polynomial (Polynomial (Polynomial ℂ))) (j₀ : ℕ), 1 ≤ j₀ →
      (∃ z ∈ U, coeffFun φfun (P'.coeff j₀) z ≠ 0) →
      (∀ z ∈ U, P'.eval₂ (eval₂RingHom (evalRingHom z) (φfun z)) (u0 z) = 0) → False) :
    letI := isDomain_analyticSubring U hUo hUc hUne
    letI : Algebra (RatFunc ℂ) (meroField U) :=
      (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring U) (meroField U) φAn)
      (algebraMap (analyticSubring U) (meroField U) (u0AnSub hUExt)) := by
  letI := isDomain_analyticSubring U hUo hUc hUne
  letI algR : Algebra (RatFunc ℂ) (meroField U) :=
    (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  intro P hrel
  set φM : meroField U := algebraMap (analyticSubring U) (meroField U) φAn with hφM
  set uM : meroField U :=
    algebraMap (analyticSubring U) (meroField U) (u0AnSub hUExt) with huM
  set n := P.natDegree with hn
  set N := (Finset.range (n + 1)).sup (fun i => (P.coeff i).natDegree) with hN
  set q : ℕ → ℕ → RatFunc ℂ := fun i j => (P.coeff i).coeff j with hq
  set Wc : ℕ → meroField U := fun j => ∑ i ∈ Finset.range (n + 1),
    algebraMap (RatFunc ℂ) (meroField U) (q i j) * φM ^ i with hWc
  have hswap : ∑ j ∈ Finset.range (N + 1), Wc j * uM ^ j = 0 := by
    have h1 : (P.map (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U).toRingHom).eval φM
        = ∑ i ∈ Finset.range (n + 1),
            (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U) (P.coeff i) * φM ^ i := by
      rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
      rfl
    have h2 : ∀ i ∈ Finset.range (n + 1),
        (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U) (P.coeff i)
          = ∑ j ∈ Finset.range (N + 1),
              algebraMap (RatFunc ℂ) (meroField U) (q i j) * uM ^ j := by
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
    have hchain : (0 : meroField U) = ∑ j ∈ Finset.range (N + 1), Wc j * uM ^ j := by
      calc (0 : meroField U)
          = (P.map (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U).toRingHom).eval φM :=
            hrel.symm
        _ = ∑ i ∈ Finset.range (n + 1),
              (aeval uM : Polynomial (RatFunc ℂ) →ₐ[RatFunc ℂ] meroField U) (P.coeff i) * φM ^ i := h1
        _ = ∑ i ∈ Finset.range (n + 1),
              (∑ j ∈ Finset.range (N + 1),
                algebraMap (RatFunc ℂ) (meroField U) (q i j) * uM ^ j) * φM ^ i :=
            Finset.sum_congr rfl fun i hi => by rw [h2 i hi]
        _ = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (N + 1),
              algebraMap (RatFunc ℂ) (meroField U) (q i j) * uM ^ j * φM ^ i :=
            Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
        _ = ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (n + 1),
              algebraMap (RatFunc ℂ) (meroField U) (q i j) * uM ^ j * φM ^ i :=
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
    set innerAn : ℕ → analyticSubring U := fun j =>
      ∑ i ∈ Finset.range (n + 1), polyToAnalytic U (q' i j) * φAn ^ i with hinnerAn
    have hinner_coe : ∀ j, ((innerAn j : analyticSubring U) : Germ (𝓟 U) ℂ)
        = ↑(fun z => ∑ i ∈ Finset.range (n + 1), (q' i j).eval z * φfun z ^ i) := by
      intro j
      simp only [hinnerAn]
      exact sum_mul_pow_coe_U (fun i => polyToAnalytic U (q' i j))
        (fun i => fun z => (q' i j).eval z) (fun i _ => rfl) φAn φfun hφval
    have hinner_alg : ∀ j ∈ Finset.range (N + 1),
        algebraMap (analyticSubring U) (meroField U) (innerAn j)
          = polyToMero U D * Wc j := by
      intro j hj
      simp only [hinnerAn]
      rw [map_sum]
      have hterm : ∀ i ∈ Finset.range (n + 1),
          algebraMap (analyticSubring U) (meroField U)
              (polyToAnalytic U (q' i j) * φAn ^ i)
            = polyToMero U D
              * (algebraMap (RatFunc ℂ) (meroField U) (q i j) * φM ^ i) := by
        intro i hi
        rw [map_mul, map_pow]
        have hcoeff : algebraMap (analyticSubring U) (meroField U)
            (polyToAnalytic U (q' i j))
              = polyToMero U D * algebraMap (RatFunc ℂ) (meroField U) (q i j) := by
          have hpm : algebraMap (analyticSubring U) (meroField U)
              (polyToAnalytic U (q' i j)) = polyToMero U (q' i j) := rfl
          rw [hpm]
          have h1 : polyToMero U (q' i j)
              = ratfuncToMero U hUo hUc hUne hUinf
                  (algebraMap (Polynomial ℂ) (RatFunc ℂ) (q' i j)) :=
            (ratfuncToMero_algebraMap_polynomial U hUo hUc hUne hUinf (q' i j)).symm
          rw [h1, halgq i hi j hj, map_mul]
          rw [ratfuncToMero_algebraMap_polynomial]
          rw [RingHom.algebraMap_toAlgebra]
        rw [hcoeff, hφM]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    have houter0 : ∑ j ∈ Finset.range (N + 1), innerAn j * (u0AnSub hUExt) ^ j
        = (0 : analyticSubring U) := by
      have halg0 : algebraMap (analyticSubring U) (meroField U)
          (∑ j ∈ Finset.range (N + 1), innerAn j * (u0AnSub hUExt) ^ j) = 0 := by
        rw [map_sum]
        have hterm : ∀ j ∈ Finset.range (N + 1),
            algebraMap (analyticSubring U) (meroField U)
                (innerAn j * (u0AnSub hUExt) ^ j)
              = polyToMero U D * (Wc j * uM ^ j) := by
          intro j hj
          rw [map_mul, map_pow, hinner_alg j hj, huM]
          ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hswap, mul_zero]
      exact (meroField_algebraMap_eq_zero_iff U hUo hUc hUne _).mp halg0
    have hpointwise : ∀ z ∈ U,
        ∑ j ∈ Finset.range (N + 1),
          (∑ i ∈ Finset.range (n + 1), (q' i j).eval z * φfun z ^ i) * u0 z ^ j = 0 :=
      (sum_mul_pow_eq_zero_iff_U innerAn
        (fun j => fun z => ∑ i ∈ Finset.range (n + 1), (q' i j).eval z * φfun z ^ i)
        (fun j _ => hinner_coe j) (u0AnSub hUExt) u0 rfl).mp houter0
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
    have hrel' : ∀ z ∈ U, P'.eval₂ (eval₂RingHom (evalRingHom z) (φfun z)) (u0 z) = 0 := by
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
    have hwitness : ∃ z ∈ U, coeffFun φfun (P'.coeff j₀) z ≠ 0 := by
      by_contra hno
      push Not at hno
      have hin0 : innerAn j₀ = 0 := by
        simp only [hinnerAn]
        refine (sum_mul_pow_eq_zero_iff_U (fun i => polyToAnalytic U (q' i j₀))
          (fun i => fun z => (q' i j₀).eval z) (fun i _ => rfl) φAn φfun hφval).mpr ?_
        intro z hz
        have := hno z hz
        rw [hcfval z] at this
        exact this
      have h1 := hinner_alg j₀ hj₀mem
      rw [hin0, map_zero] at h1
      have hDm : polyToMero U D ≠ 0 := by
        intro h0
        exact hDne (polyToMero_injective U hUo hUc hUne hUinf
          (h0.trans (map_zero _).symm))
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact hDm h
      · exact hWne h
    obtain ⟨z₀, hz₀, hcw⟩ := hwitness
    exact (engine P' j₀ hj₀pos ⟨z₀, hz₀, hcw⟩ hrel').elim

/-- **`u₀ ⟂ phiB b` — UNCONDITIONAL algebraic independence for EVERY `‖b‖ > 2+√2`.**  The
window capstone at the SHARP threshold: in the meromorphic field of the b-dependent window
annulus `{1 < ‖z‖ < rB b}`, the Böttcher window branch of any parameter `‖b‖ > 2+√2` and the
c-velocity `u₀` satisfy no nonzero bivariate polynomial relation over `ℂ(z)`.  No tower
certificate, no `GBExt` clause, no open input. -/
theorem u0_phiB_independence {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) :
    letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
      (annWB_nonempty hb)
    letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
      (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb) (annWB_nonempty hb)
        (annWB_infinite hb)).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring (annWB b)) (meroField (annWB b)) (phiBAn b hb))
      (algebraMap (analyticSubring (annWB b)) (meroField (annWB b))
        (u0AnSub annWB_subset_Ext)) := by
  letI := isDomain_analyticSubring (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb)
    (annWB_nonempty hb)
  letI : Algebra (RatFunc ℂ) (meroField (annWB b)) :=
    (ratfuncToMero (annWB b) (isOpen_annWB b) (isPreconnected_annWB hb) (annWB_nonempty hb)
      (annWB_infinite hb)).toAlgebra
  exact u0_window_independence_of_transcendental_engine (isOpen_annWB b)
    (isPreconnected_annWB hb) (annWB_nonempty hb) (annWB_infinite hb) annWB_subset_Ext
    (phiB b) (phiBAn b hb) rfl
    (phiB_transcendental hb)
    (fun P' j₀ hj₀ hnd hrel => u0_phiB_no_relation_nondegenerate hb P' hj₀ hnd
      (isOpen_annWB b) (annWB_nonempty hb) (fun z hz => hz) hrel)

end U0PhiLargeCapstone
