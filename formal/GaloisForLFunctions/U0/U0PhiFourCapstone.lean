/-
# `u₀ ⟂ phiFour` — the unconditional `b = 4` window capstone

The full algebraic independence `NoRelation ℂ(z) (phiFour) (u₀)` in the meromorphic field of the
window annulus `annW = {1 < ‖z‖ < 21/20}` — with NO hypothesis.  Assembly of the two proven
halves:

* a relation genuinely involving `u₀` (some positive-`u₀`-degree coefficient with nonvanishing
  germ) dies against the natural-boundary window engine
  (`U0PhiFourWindow.u0_phiFour_no_relation_nondegenerate`), after clearing the `ℂ(z)`-denominators
  into polynomial data and descending the germ identity to a pointwise one;
* a relation whose positive-`u₀`-degree columns all vanish as germs collapses, column by column,
  against `U0PhiFourDescent.phiFour_transcendental` (the dyadic-pullback descent onto
  `Bottcher.bottcher_transcendental_far`), forcing every coefficient of `P` to vanish.

This realizes the `u0_phi_independence` card conclusion **unconditionally at `b = 4`** on the
constructed window carrier — no tower certificate, no `GBExt` clause, no open input.
-/
import GaloisForLFunctions.U0.U0PhiFourDescent
import GaloisForLFunctions.U0.U0WindowNormalization
import GaloisForLFunctions.U0.U0MeroCarrier

open Complex Set Metric Polynomial Filter Topology Bottcher
open U0 U0NaturalBoundary U0PhiFourWindow U0PhiFourFarCarrier U0PhiFourDescent U0MeroCarrier
open U0WindowNormalization

namespace U0PhiFourCapstone

/-! ## Germ realization of layered sums -/

/-- Values of a layered sum `∑ eⱼ·bʲ` of analytic germs: if each `eⱼ` is the germ of `gⱼ` and `b`
the germ of `f`, the sum is the germ of `z ↦ ∑ gⱼ(z)·f(z)ʲ`. -/
theorem sum_mul_pow_coe {k : ℕ} (e : ℕ → analyticSubring annW) (g : ℕ → ℂ → ℂ)
    (hval : ∀ j ∈ Finset.range k, ((e j : analyticSubring annW) : Germ (𝓟 annW) ℂ) = ↑(g j))
    (b : analyticSubring annW) (f : ℂ → ℂ)
    (hb : ((b : analyticSubring annW) : Germ (𝓟 annW) ℂ) = ↑f) :
    ((∑ j ∈ Finset.range k, e j * b ^ j : analyticSubring annW) : Germ (𝓟 annW) ℂ)
      = ↑(fun z => ∑ j ∈ Finset.range k, g j z * f z ^ j) := by
  have h1 : ((∑ j ∈ Finset.range k, e j * b ^ j : analyticSubring annW) : Germ (𝓟 annW) ℂ)
      = ∑ j ∈ Finset.range k,
          ((e j : analyticSubring annW) : Germ (𝓟 annW) ℂ)
            * (((b : analyticSubring annW) : Germ (𝓟 annW) ℂ)) ^ j := by
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun j _ => by rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
  have h2 : (fun z => ∑ j ∈ Finset.range k, g j z * f z ^ j)
      = ∑ j ∈ Finset.range k, (g j * f ^ j) := by
    funext z
    rw [Finset.sum_apply]
    rfl
  rw [h1, h2]
  have h3 : ((↑(∑ j ∈ Finset.range k, (g j * f ^ j)) : Germ (𝓟 annW) ℂ))
      = ∑ j ∈ Finset.range k, (↑(g j * f ^ j) : Germ (𝓟 annW) ℂ) :=
    map_sum (Germ.coeRingHom (𝓟 annW)) _ _
  rw [h3]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hval j hj, hb]
  rw [← Germ.coe_pow, ← Germ.coe_mul]

/-- Vanishing bridge: the layered analytic-germ sum is zero iff its pointwise realization
vanishes on the annulus. -/
theorem sum_mul_pow_eq_zero_iff {k : ℕ} (e : ℕ → analyticSubring annW) (g : ℕ → ℂ → ℂ)
    (hval : ∀ j ∈ Finset.range k, ((e j : analyticSubring annW) : Germ (𝓟 annW) ℂ) = ↑(g j))
    (b : analyticSubring annW) (f : ℂ → ℂ)
    (hb : ((b : analyticSubring annW) : Germ (𝓟 annW) ℂ) = ↑f) :
    (∑ j ∈ Finset.range k, e j * b ^ j = (0 : analyticSubring annW))
      ↔ ∀ z ∈ annW, ∑ j ∈ Finset.range k, g j z * f z ^ j = 0 := by
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero, sum_mul_pow_coe e g hval b f hb]
  rw [← Germ.coe_zero, Germ.coe_eq]
  constructor
  · intro h z hz
    exact eventually_principal.mp h z hz
  · intro h
    apply eventually_principal.mpr
    intro z hz
    exact h z hz

/-! ## The capstone -/

/-- **`u₀ ⟂ phiFour` — UNCONDITIONAL algebraic independence at `b = 4`.**  In the meromorphic
field of the window annulus `{1 < ‖z‖ < 21/20}`, the constructed Böttcher window branch `phiFour`
and the c-velocity `u₀` satisfy no nonzero bivariate polynomial relation over `ℂ(z)`.  No tower
certificate, no window hypothesis, no `GBExt` clause — every analytic input is proven in-tree. -/
theorem u0_phiFour_independence :
    letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
    letI : Algebra (RatFunc ℂ) (meroField annW) :=
      (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
    NoRelation (RatFunc ℂ)
      (algebraMap (analyticSubring annW) (meroField annW) phiAnnAn)
      (algebraMap (analyticSubring annW) (meroField annW) (u0AnSub annW_subset_Ext)) := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  letI algR : Algebra (RatFunc ℂ) (meroField annW) :=
    (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
  intro P hrel
  set φM : meroField annW := algebraMap (analyticSubring annW) (meroField annW) phiAnnAn with hφM
  set uM : meroField annW :=
    algebraMap (analyticSubring annW) (meroField annW) (u0AnSub annW_subset_Ext) with huM
  set n := P.natDegree with hn
  set N := (Finset.range (n + 1)).sup (fun i => (P.coeff i).natDegree) with hN
  set q : ℕ → ℕ → RatFunc ℂ := fun i j => (P.coeff i).coeff j with hq
  set Wc : ℕ → meroField annW := fun j => ∑ i ∈ Finset.range (n + 1),
    algebraMap (RatFunc ℂ) (meroField annW) (q i j) * φM ^ i with hWc
  -- the germ-level column decomposition of the relation
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
  -- transcendence of the window branch (the descent theorem)
  have htransc := phiFour_transcendental
  rw [transcendental_iff] at htransc
  by_cases hall : ∀ j ∈ Finset.range (N + 1), 1 ≤ j → Wc j = 0
  · -- every positive column vanishes: transcendence collapses all columns, P = 0
    have hW0 : Wc 0 = 0 := by
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
        apply htransc
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
  · -- a genuine u₀-column survives: clear denominators, go pointwise, hit the window engine
    push Not at hall
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
    -- the analytic realizations
    set innerAn : ℕ → analyticSubring annW := fun j =>
      ∑ i ∈ Finset.range (n + 1), polyToAnalytic annW (q' i j) * phiAnnAn ^ i with hinnerAn
    have hinner_coe : ∀ j, ((innerAn j : analyticSubring annW) : Germ (𝓟 annW) ℂ)
        = ↑(fun z => ∑ i ∈ Finset.range (n + 1), (q' i j).eval z * phiFour z ^ i) := by
      intro j
      simp only [hinnerAn]
      exact sum_mul_pow_coe (fun i => polyToAnalytic annW (q' i j))
        (fun i => fun z => (q' i j).eval z) (fun i _ => rfl) phiAnnAn phiFour rfl
    have hinner_alg : ∀ j ∈ Finset.range (N + 1),
        algebraMap (analyticSubring annW) (meroField annW) (innerAn j)
          = polyToMero annW D * Wc j := by
      intro j hj
      simp only [hinnerAn]
      rw [map_sum]
      have hterm : ∀ i ∈ Finset.range (n + 1),
          algebraMap (analyticSubring annW) (meroField annW)
              (polyToAnalytic annW (q' i j) * phiAnnAn ^ i)
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
    -- the germ relation, cleared: the outer layered sum vanishes
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
      have := (meroField_algebraMap_eq_zero_iff annW isOpen_annW isPreconnected_annW
        annW_nonempty _).mp halg0
      exact this
    have hpointwise : ∀ z ∈ annW,
        ∑ j ∈ Finset.range (N + 1),
          (∑ i ∈ Finset.range (n + 1), (q' i j).eval z * phiFour z ^ i) * u0 z ^ j = 0 :=
      (sum_mul_pow_eq_zero_iff innerAn
        (fun j => fun z => ∑ i ∈ Finset.range (n + 1), (q' i j).eval z * phiFour z ^ i)
        (fun j _ => hinner_coe j) (u0AnSub annW_subset_Ext) u0 rfl).mp houter0
    -- the engine polynomial
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
        coeffFun phiFour p z = p.eval₂ (evalRingHom z) (phiFour z) := fun _ _ => rfl
    have hcfval : ∀ z, coeffFun phiFour (P'.coeff j₀) z
        = ∑ i ∈ Finset.range (n + 1), (q' i j₀).eval z * phiFour z ^ i := by
      intro z
      rw [hcf, hP'coeff, eval₂_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [eval₂_monomial, coe_evalRingHom]
    have hrel' : ∀ z ∈ annW, P'.eval₂ (eval₂RingHom (evalRingHom z) (phiFour z)) (u0 z) = 0 := by
      intro z hz
      rw [hP', eval₂_finsetSum]
      have hterm : ∀ j ∈ Finset.range (N + 1),
          (monomial j (∑ i ∈ Finset.range (n + 1), monomial i (q' i j))).eval₂
              (eval₂RingHom (evalRingHom z) (phiFour z)) (u0 z)
            = (∑ i ∈ Finset.range (n + 1), (q' i j).eval z * phiFour z ^ i) * u0 z ^ j := by
        intro j _
        rw [eval₂_monomial]
        congr 1
        rw [coe_eval₂RingHom, eval₂_finsetSum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [eval₂_monomial, coe_evalRingHom]
      rw [Finset.sum_congr rfl hterm]
      exact hpointwise z hz
    -- the nondegeneracy witness
    have hwitness : ∃ z ∈ Metric.ball (0 : ℂ) (21 / 20) ∩ Ext,
        coeffFun phiFour (P'.coeff j₀) z ≠ 0 := by
      by_contra hno
      push Not at hno
      have hin0 : innerAn j₀ = 0 := by
        simp only [hinnerAn]
        refine (sum_mul_pow_eq_zero_iff (fun i => polyToAnalytic annW (q' i j₀))
          (fun i => fun z => (q' i j₀).eval z) (fun i _ => rfl) phiAnnAn phiFour rfl).mpr ?_
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
    exact (u0_phiFour_no_relation_nondegenerate P' hj₀pos ⟨z₀, hz₀, hcw⟩
      isOpen_annW annW_nonempty (fun z hz => hz) hrel').elim

end U0PhiFourCapstone
