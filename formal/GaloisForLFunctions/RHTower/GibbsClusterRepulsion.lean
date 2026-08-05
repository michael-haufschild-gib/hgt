import Mathlib
import GaloisForLFunctions.RHTower.GibbsParityVortex

/-!
# Two-scale repulsion of the parity cluster: the locking law

The cutoff recursion of the squarefree Gibbs gas forces an exact relation between the
separation of the parity cluster and the Möbius–Laplace current:

* `gibbs_current_insert` — the **current two-scale law** `J_{S∪p}(x) = J_S(x) − J_S(px)`:
  the current is the ladder generator, and its linearization is the totient recursion
  `φ_{S∪p} = (p−1)·φ_S`;
* `gibbsDiag_zero_parity` — at coupling zero the parity cluster fully degenerates
  (`P_S(0, −1+w) = w^k`);
* `tendsto_pairDisc_div_current` / `tendsto_tripleDisc_div_sq_current` — the
  **repulsion–current locking law** at orders two and three: `Disc₂/J → −4` and
  `Disc₃/J² → −27`.  The parity-cluster discriminant is asymptotically a pure power of
  the current: cluster repulsion is not an invariant independent of the current;
* `eventual_current_sq_le_abs_tripleDisc` — the **reversed rung**: `J² ≤ |Disc₃|` for all
  small couplings.  Anomalous current cancellation can only come from anomalous cluster
  collapse: a graded route to parity cancellation runs through discriminant *upper*
  bounds, not repulsion lower bounds.
-/

namespace RHTower.GibbsGas

open Real Filter

/-- **The current two-scale law**: the Möbius–Laplace current is the ladder generator. -/
theorem gibbs_current_insert (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    gibbsDiag (insert p S) x (-1)
      = gibbsDiag S x (-1) - gibbsDiag S ((p : ℝ) * x) (-1) := by
  rw [gibbsDiag_insert p S hp]
  ring

/-- At coupling zero the parity cluster fully degenerates. -/
theorem gibbsDiag_zero_parity (S : Finset ℕ) (w : ℝ) :
    gibbsDiag S 0 (-1 + w) = w ^ S.card := by
  rw [gibbsDiag_zero]
  norm_num

/-- Slope limits along the punctured right neighbourhood of coupling zero. -/
theorem slope_limit_right (g : ℝ → ℝ) (d : ℝ) (hg0 : g 0 = 0) (hgd : HasDerivAt g d 0) :
    Filter.Tendsto (fun x => g x / x) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds d) := by
  have hmono : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) {y | y ≠ 0} :=
    nhdsWithin_mono 0 (fun y hy => ne_of_gt hy)
  have h1 := hasDerivAt_iff_tendsto_slope.mp hgd
  have h2 : Filter.Tendsto (fun x => g x / x)
      (nhdsWithin (0:ℝ) {y | y ≠ 0}) (nhds d) := by
    refine h1.congr fun y => ?_
    simp [slope_def_field, hg0]
  exact h2.mono_left hmono

/-- The pair current has slope `−(p−1)(q−1)` at coupling zero. -/
theorem tendsto_pair_current_div (p q : ℕ) (hpq : p ≠ q) :
    Filter.Tendsto (fun x => gibbsDiag {p, q} x (-1) / x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (-(((p:ℝ) - 1) * ((q:ℝ) - 1)))) := by
  have hnotmem : p ∉ ({q} : Finset ℕ) := by simp [hpq]
  have hcard : ({p, q} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem hnotmem, Finset.card_singleton]
  have hprod : ∏ a ∈ ({p, q} : Finset ℕ), ((a:ℝ) - 1)
      = ((p:ℝ) - 1) * ((q:ℝ) - 1) := by
    rw [Finset.prod_insert hnotmem, Finset.prod_singleton]
  have hd := hasDerivAt_gibbs_current ({p, q} : Finset ℕ)
  rw [hcard, hprod] at hd
  have hval : ((-1:ℝ)) ^ (2 + 1) * (((p:ℝ) - 1) * ((q:ℝ) - 1))
      = -(((p:ℝ) - 1) * ((q:ℝ) - 1)) := by ring
  rw [hval] at hd
  have h0 : gibbsDiag {p, q} 0 (-1) = 0 := by
    rw [gibbsDiag_zero, hcard]
    norm_num
  exact slope_limit_right _ _ h0 hd

/-- The triple current has slope `(p−1)(q−1)(r−1)` — the totient — at coupling zero. -/
theorem tendsto_triple_current_div (p q r : ℕ)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Filter.Tendsto (fun x => gibbsDiag {p, q, r} x (-1) / x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhds (((p:ℝ) - 1) * (((q:ℝ) - 1) * ((r:ℝ) - 1)))) := by
  have hmp : p ∉ ({q, r} : Finset ℕ) := by simp [hpq, hpr]
  have hmq : q ∉ ({r} : Finset ℕ) := by simp [hqr]
  have hcard : ({p, q, r} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem hmp, Finset.card_insert_of_notMem hmq,
      Finset.card_singleton]
  have hprod : ∏ a ∈ ({p, q, r} : Finset ℕ), ((a:ℝ) - 1)
      = ((p:ℝ) - 1) * (((q:ℝ) - 1) * ((r:ℝ) - 1)) := by
    rw [Finset.prod_insert hmp, Finset.prod_insert hmq, Finset.prod_singleton]
  have hd := hasDerivAt_gibbs_current ({p, q, r} : Finset ℕ)
  rw [hcard, hprod] at hd
  have hval : ((-1:ℝ)) ^ (3 + 1) * (((p:ℝ) - 1) * (((q:ℝ) - 1) * ((r:ℝ) - 1)))
      = ((p:ℝ) - 1) * (((q:ℝ) - 1) * ((r:ℝ) - 1)) := by ring
  rw [hval] at hd
  have h0 : gibbsDiag {p, q, r} 0 (-1) = 0 := by
    rw [gibbsDiag_zero, hcard]
    norm_num
  exact slope_limit_right _ _ h0 hd

/-! ## The order-two locking law -/

/-- The parity jets of the pair gas. -/
noncomputable def pairJet0 (p q : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) - (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)))
    + Real.exp (-((q:ℝ)*((p:ℝ)*x)))

noncomputable def pairJet1 (p q : ℕ) (x : ℝ) : ℝ :=
  (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)))
    - 2 * Real.exp (-((q:ℝ)*((p:ℝ)*x)))

noncomputable def pairJet2 (p q : ℕ) (x : ℝ) : ℝ := Real.exp (-((q:ℝ)*((p:ℝ)*x)))

/-- The discriminant of the pair gas at the parity point. -/
noncomputable def pairDisc (p q : ℕ) (x : ℝ) : ℝ :=
  pairJet1 p q x ^ 2 - 4 * pairJet2 p q x * pairJet0 p q x

theorem gibbsDiag_pair_jet (p q : ℕ) (hpq : p ≠ q) (x w : ℝ) :
    gibbsDiag {p, q} x (-1 + w)
      = pairJet2 p q x * w^2 + pairJet1 p q x * w + pairJet0 p q x := by
  have hpq' : p ∉ ({q} : Finset ℕ) := by simp [hpq]
  rw [gibbsDiag_insert p {q} hpq', gibbsDiag_singleton, gibbsDiag_singleton,
    pairJet0, pairJet1, pairJet2]
  ring

theorem pairJet0_eq_current (p q : ℕ) (hpq : p ≠ q) (x : ℝ) :
    pairJet0 p q x = gibbsDiag {p, q} x (-1) := by
  have h := gibbsDiag_pair_jet p q hpq x 0
  simpa using h.symm

/-- **The order-two locking law**: `Disc₂ / J → −4`. -/
theorem tendsto_pairDisc_div_current (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hpq : p ≠ q) :
    Filter.Tendsto (fun x => pairDisc p q x / gibbsDiag {p, q} x (-1))
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-4)) := by
  set φ : ℝ := ((p:ℝ) - 1) * ((q:ℝ) - 1) with hφ
  have hφ0 : 0 < φ := by
    rw [hφ]
    have h1 : (0:ℝ) < (p:ℝ) - 1 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      linarith
    have h2 : (0:ℝ) < (q:ℝ) - 1 := by
      have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith
    exact mul_pos h1 h2
  have hJx : Filter.Tendsto (fun x => gibbsDiag {p, q} x (-1) / x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-φ)) := tendsto_pair_current_div p q hpq
  have hs0 : Filter.Tendsto (fun x => pairJet0 p q x / x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-φ)) := by
    refine hJx.congr fun x => ?_
    rw [pairJet0_eq_current p q hpq]
  have hj10 : pairJet1 p q 0 = 0 := by rw [pairJet1]; norm_num [Real.exp_zero]
  have hd1 : DifferentiableAt ℝ (pairJet1 p q) 0 := by
    rw [show pairJet1 p q = fun x => (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)))
      - 2 * Real.exp (-((q:ℝ)*((p:ℝ)*x))) from rfl]
    fun_prop
  have hs1 := slope_limit_right (pairJet1 p q) (deriv (pairJet1 p q) 0) hj10
    hd1.hasDerivAt
  have hj2c : Filter.Tendsto (pairJet2 p q) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hc : Continuous (pairJet2 p q) := by
      rw [show pairJet2 p q = fun x => Real.exp (-((q:ℝ)*((p:ℝ)*x))) from rfl]
      fun_prop
    have h1 := hc.tendsto 0
    have h20 : pairJet2 p q 0 = 1 := by rw [pairJet2]; norm_num [Real.exp_zero]
    rw [h20] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hxlim : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hxpos : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx
  have hDx : Filter.Tendsto (fun x => pairDisc p q x / x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (4*φ)) := by
    have htmp : Filter.Tendsto (fun x =>
        x * (pairJet1 p q x / x)^2 - 4 * pairJet2 p q x * (pairJet0 p q x / x))
        (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (0 * (deriv (pairJet1 p q) 0)^2 - 4 * 1 * (-φ))) :=
      (hxlim.mul (hs1.pow 2)).sub ((Filter.Tendsto.const_mul 4 hj2c).mul hs0)
    have hval : (0 * (deriv (pairJet1 p q) 0)^2 - 4 * 1 * (-φ)) = 4*φ := by ring
    rw [hval] at htmp
    refine htmp.congr' ?_
    filter_upwards [hxpos] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    rw [pairDisc]
    field_simp
  have hdiv := hDx.div hJx (by
    intro h
    rw [neg_eq_zero] at h
    exact (ne_of_gt hφ0) h)
  have hval2 : (4*φ) / (-φ) = -4 := by
    rw [div_eq_iff (neg_ne_zero.mpr (ne_of_gt hφ0))]
    ring
  rw [hval2] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hxpos] with x hx
  have hxne : x ≠ 0 := ne_of_gt hx
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hxne]

/-! ## The order-three locking law and the reversed rung -/

/-- The parity jets of the triple gas. -/
noncomputable def tripleJet0 (p q r : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x)
    - (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x)))
    + (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
        + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
    - Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x))))

noncomputable def tripleJet1 (p q r : ℕ) (x : ℝ) : ℝ :=
  (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x)))
    - 2 * (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
        + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
    + 3 * Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x))))

noncomputable def tripleJet2 (p q r : ℕ) (x : ℝ) : ℝ :=
  (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
      + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
    - 3 * Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x))))

noncomputable def tripleJet3 (p q r : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x))))

/-- The discriminant of the triple gas at the parity point. -/
noncomputable def tripleDisc (p q r : ℕ) (x : ℝ) : ℝ :=
  18 * tripleJet3 p q r x * tripleJet2 p q r x * tripleJet1 p q r x * tripleJet0 p q r x
    - 4 * (tripleJet2 p q r x)^3 * tripleJet0 p q r x
    + (tripleJet2 p q r x)^2 * (tripleJet1 p q r x)^2
    - 4 * tripleJet3 p q r x * (tripleJet1 p q r x)^3
    - 27 * (tripleJet3 p q r x)^2 * (tripleJet0 p q r x)^2

theorem gibbsDiag_triple_jet (p q r : ℕ) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (x w : ℝ) :
    gibbsDiag {p, q, r} x (-1 + w)
      = tripleJet3 p q r x * w^3 + tripleJet2 p q r x * w^2
        + tripleJet1 p q r x * w + tripleJet0 p q r x := by
  have hqr' : q ∉ ({r} : Finset ℕ) := by simp [hqr]
  have hp' : p ∉ ({q, r} : Finset ℕ) := by simp [hpq, hpr]
  rw [gibbsDiag_insert p {q, r} hp', gibbsDiag_insert q {r} hqr',
    gibbsDiag_insert q {r} hqr', gibbsDiag_singleton, gibbsDiag_singleton,
    gibbsDiag_singleton, gibbsDiag_singleton,
    tripleJet0, tripleJet1, tripleJet2, tripleJet3]
  ring

theorem tripleJet0_eq_current (p q r : ℕ) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (x : ℝ) :
    tripleJet0 p q r x = gibbsDiag {p, q, r} x (-1) := by
  have h := gibbsDiag_triple_jet p q r hpq hpr hqr x 0
  simpa using h.symm

/-- **The order-three locking law**: `Disc₃ / J² → −27`.  The parity-cluster discriminant
is asymptotically a pure power of the Möbius–Laplace current. -/
theorem tendsto_tripleDisc_div_sq_current (p q r : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Filter.Tendsto
      (fun x => tripleDisc p q r x / (gibbsDiag {p, q, r} x (-1))^2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-27)) := by
  set φ : ℝ := ((p:ℝ) - 1) * (((q:ℝ) - 1) * ((r:ℝ) - 1)) with hφ
  have hφ0 : 0 < φ := by
    rw [hφ]
    have h1 : (0:ℝ) < (p:ℝ) - 1 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      linarith
    have h2 : (0:ℝ) < (q:ℝ) - 1 := by
      have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith
    have h3 : (0:ℝ) < (r:ℝ) - 1 := by
      have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      linarith
    exact mul_pos h1 (mul_pos h2 h3)
  have hJx : Filter.Tendsto (fun x => gibbsDiag {p, q, r} x (-1) / x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds φ) :=
    tendsto_triple_current_div p q r hpq hpr hqr
  have hs0 : Filter.Tendsto (fun x => tripleJet0 p q r x / x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds φ) := by
    refine hJx.congr fun x => ?_
    rw [tripleJet0_eq_current p q r hpq hpr hqr]
  have hj10 : tripleJet1 p q r 0 = 0 := by rw [tripleJet1]; norm_num [Real.exp_zero]
  have hj20 : tripleJet2 p q r 0 = 0 := by rw [tripleJet2]; norm_num [Real.exp_zero]
  have hd1 : DifferentiableAt ℝ (tripleJet1 p q r) 0 := by
    rw [show tripleJet1 p q r = fun x =>
        (Real.exp (-((p:ℝ)*x)) + Real.exp (-((q:ℝ)*x)) + Real.exp (-((r:ℝ)*x)))
          - 2 * (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
              + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
          + 3 * Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) from rfl]
    fun_prop
  have hd2 : DifferentiableAt ℝ (tripleJet2 p q r) 0 := by
    rw [show tripleJet2 p q r = fun x =>
        (Real.exp (-((q:ℝ)*((p:ℝ)*x))) + Real.exp (-((r:ℝ)*((p:ℝ)*x)))
            + Real.exp (-((r:ℝ)*((q:ℝ)*x))))
          - 3 * Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) from rfl]
    fun_prop
  have hs1 := slope_limit_right (tripleJet1 p q r) (deriv (tripleJet1 p q r) 0) hj10
    hd1.hasDerivAt
  have hs2 := slope_limit_right (tripleJet2 p q r) (deriv (tripleJet2 p q r) 0) hj20
    hd2.hasDerivAt
  have hj3c : Filter.Tendsto (tripleJet3 p q r)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 1) := by
    have hc : Continuous (tripleJet3 p q r) := by
      rw [show tripleJet3 p q r
        = fun x => Real.exp (-((r:ℝ)*((q:ℝ)*((p:ℝ)*x)))) from rfl]
      fun_prop
    have h1 := hc.tendsto 0
    have h30 : tripleJet3 p q r 0 = 1 := by rw [tripleJet3]; norm_num [Real.exp_zero]
    rw [h30] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hxlim : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0) :=
    Filter.tendsto_id.mono_left nhdsWithin_le_nhds
  have hxpos : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx
  have hDx2 : Filter.Tendsto (fun x => tripleDisc p q r x / x^2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-27 * φ^2)) := by
    have htmp : Filter.Tendsto (fun x =>
        x * (18 * tripleJet3 p q r x * (tripleJet2 p q r x / x)
              * (tripleJet1 p q r x / x) * (tripleJet0 p q r x / x))
          - x^2 * (4 * (tripleJet2 p q r x / x)^3 * (tripleJet0 p q r x / x))
          + x^2 * ((tripleJet2 p q r x / x)^2 * (tripleJet1 p q r x / x)^2)
          - x * (4 * tripleJet3 p q r x * (tripleJet1 p q r x / x)^3)
          - 27 * (tripleJet3 p q r x)^2 * (tripleJet0 p q r x / x)^2)
        (nhdsWithin (0:ℝ) (Set.Ioi 0))
        (nhds (0 * (18 * 1 * (deriv (tripleJet2 p q r) 0)
              * (deriv (tripleJet1 p q r) 0) * φ)
          - 0^2 * (4 * (deriv (tripleJet2 p q r) 0)^3 * φ)
          + 0^2 * ((deriv (tripleJet2 p q r) 0)^2 * (deriv (tripleJet1 p q r) 0)^2)
          - 0 * (4 * 1 * (deriv (tripleJet1 p q r) 0)^3)
          - 27 * 1^2 * φ^2)) :=
      (((((hxlim.mul ((((Filter.Tendsto.const_mul 18 hj3c).mul hs2).mul hs1).mul
        hs0)).sub ((hxlim.pow 2).mul ((Filter.Tendsto.const_mul 4 (hs2.pow 3)).mul
        hs0))).add ((hxlim.pow 2).mul ((hs2.pow 2).mul (hs1.pow 2)))).sub
        (hxlim.mul ((Filter.Tendsto.const_mul 4 hj3c).mul (hs1.pow 3)))).sub
        ((Filter.Tendsto.const_mul 27 (hj3c.pow 2)).mul (hs0.pow 2)))
    have hval : (0 * (18 * 1 * (deriv (tripleJet2 p q r) 0)
          * (deriv (tripleJet1 p q r) 0) * φ)
        - 0^2 * (4 * (deriv (tripleJet2 p q r) 0)^3 * φ)
        + 0^2 * ((deriv (tripleJet2 p q r) 0)^2 * (deriv (tripleJet1 p q r) 0)^2)
        - 0 * (4 * 1 * (deriv (tripleJet1 p q r) 0)^3)
        - 27 * 1^2 * φ^2) = -27 * φ^2 := by ring
    rw [hval] at htmp
    refine htmp.congr' ?_
    filter_upwards [hxpos] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    rw [tripleDisc]
    field_simp
  have hJx2 : Filter.Tendsto (fun x => (gibbsDiag {p, q, r} x (-1) / x)^2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (φ^2)) := hJx.pow 2
  have hdiv := hDx2.div hJx2 (by positivity)
  have hval2 : (-27 * φ^2) / (φ^2) = -27 := by
    rw [div_eq_iff (by positivity : (φ:ℝ)^2 ≠ 0)]
  rw [hval2] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hxpos] with x hx
  have hxne : x ≠ 0 := ne_of_gt hx
  simp only [Pi.div_apply]
  rw [div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 hxne)]

/-- **The reversed rung.**  For all small couplings the squared Möbius–Laplace current is
dominated by the parity-cluster discriminant: anomalous current cancellation can only come
from anomalous cluster collapse.  The graded route to parity cancellation runs through
discriminant *upper* bounds, not repulsion lower bounds. -/
theorem eventual_current_sq_le_abs_tripleDisc (p q r : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (gibbsDiag {p, q, r} x (-1))^2 ≤ |tripleDisc p q r x| := by
  have hlock := tendsto_tripleDisc_div_sq_current p q r hp hq hr hpq hpr hqr
  have hev1 : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0),
      tripleDisc p q r x / (gibbsDiag {p, q, r} x (-1))^2 < -1 :=
    hlock.eventually (eventually_lt_nhds (by norm_num : (-27:ℝ) < -1))
  set φ : ℝ := ((p:ℝ) - 1) * (((q:ℝ) - 1) * ((r:ℝ) - 1)) with hφ
  have hφ0 : 0 < φ := by
    rw [hφ]
    have h1 : (0:ℝ) < (p:ℝ) - 1 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
      linarith
    have h2 : (0:ℝ) < (q:ℝ) - 1 := by
      have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith
    have h3 : (0:ℝ) < (r:ℝ) - 1 := by
      have : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      linarith
    exact mul_pos h1 (mul_pos h2 h3)
  have hJx : Filter.Tendsto (fun x => gibbsDiag {p, q, r} x (-1) / x)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds φ) :=
    tendsto_triple_current_div p q r hpq hpr hqr
  have hevJ : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0),
      φ/2 < gibbsDiag {p, q, r} x (-1) / x :=
    hJx.eventually (eventually_gt_nhds (by linarith))
  have hxpos : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx
  filter_upwards [hev1, hevJ, hxpos] with x h1 h2 hx
  have hJpos : 0 < gibbsDiag {p, q, r} x (-1) := by
    have hxne : x ≠ 0 := ne_of_gt hx
    have hquot : 0 < gibbsDiag {p, q, r} x (-1) / x := lt_trans (by linarith) h2
    have hrw : gibbsDiag {p, q, r} x (-1)
        = (gibbsDiag {p, q, r} x (-1) / x) * x := (div_mul_cancel₀ _ hxne).symm
    rw [hrw]
    exact mul_pos hquot hx
  have hJ2 : 0 < (gibbsDiag {p, q, r} x (-1))^2 := by positivity
  have hΔlt : tripleDisc p q r x < -(gibbsDiag {p, q, r} x (-1))^2 := by
    have h3 := (div_lt_iff₀ hJ2).mp h1
    linarith
  have hΔneg : tripleDisc p q r x < 0 := lt_trans hΔlt (by linarith)
  rw [abs_of_neg hΔneg]
  linarith

end RHTower.GibbsGas
