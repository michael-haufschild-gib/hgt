import GaloisForLFunctions.HTGeometry.EllipticMeromorphicOrderTools
import GaloisForLFunctions.HTGeometry.PeriodRigidity
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# Even lattice-periodic functions with poles only at the lattice are polynomials in `℘`

An even meromorphic function invariant under a period lattice and analytic off that lattice is a
polynomial in the Weierstrass `℘` function of the lattice.

The proof is the classical descending induction on the pole order at the origin.  Evenness forces
that order to be even, say `-2k`; the function `℘ ^ k` has exactly that order there, so one multiple
of it cancels the leading Laurent term, and the difference is again even, lattice-periodic and
analytic off the lattice, with pole order at most `2k - 2`.  When no pole is left the function is
constant by elliptic Liouville.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable (L : PeriodPair)

/-- The lattice contains the origin. -/
theorem zero_mem_lattice : (0 : ℂ) ∈ L.lattice := Submodule.zero_mem _

/-- `℘` is periodic under every lattice vector. -/
theorem weierstrassP_periodic {p : ℂ} (hp : p ∈ L.lattice) :
    Function.Periodic L.weierstrassP p := L.periodic_weierstrassP ⟨p, hp⟩

/-- Away from the lattice `℘` is analytic, hence of nonnegative order. -/
theorem nonneg_meromorphicOrderAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    0 ≤ meromorphicOrderAt L.weierstrassP z :=
  (L.analyticOnNhd_weierstrassP z hz).meromorphicOrderAt_nonneg

/-- The `k`-th power of `℘` has a pole of order exactly `2k` at the origin. -/
theorem meromorphicOrderAt_weierstrassP_pow_zero (k : ℕ) :
    meromorphicOrderAt (fun z => L.weierstrassP z ^ k) 0 = ((-(2 * k) : ℤ) : WithTop ℤ) := by
  induction k with
  | zero =>
      have hfun : (fun z : ℂ => L.weierstrassP z ^ (0 : ℕ)) = fun _ : ℂ => (1 : ℂ) := by
        funext z; simp
      have hord0 : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) 0 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr one_ne_zero)
      rw [hfun, (analyticAt_const (v := (1 : ℂ)) (x := (0 : ℂ))).meromorphicOrderAt_eq, hord0]
      simp
  | succ k ih =>
      have hkmer : MeromorphicAt (fun z => L.weierstrassP z ^ k) 0 :=
        (L.meromorphic_weierstrassP 0).pow k
      have hsplit : (fun z : ℂ => L.weierstrassP z ^ (k + 1))
          = fun z : ℂ => (L.weierstrassP z ^ k) * L.weierstrassP z := by
        funext z; ring
      rw [hsplit, fun_meromorphicOrderAt_mul hkmer (L.meromorphic_weierstrassP 0), ih,
        L.order_weierstrassP 0 (zero_mem_lattice L)]
      have hneg2 : (-2 : WithTop ℤ) = (((-2 : ℤ)) : WithTop ℤ) := by norm_num
      rw [hneg2, ← WithTop.coe_add]
      congr 1
      push_cast
      ring

/-- **Even lattice-periodic functions with poles only on the lattice are polynomials in `℘`**,
proved by descending induction on the pole order at the origin. -/
theorem exists_polynomial_eval_weierstrassP_of_orderBound (k : ℕ) :
    ∀ F : ℂ → ℂ, (∀ z, MeromorphicAt F z) →
      (∀ p ∈ L.lattice, Function.Periodic F p) → (∀ z, F (-z) = F z) →
      (∀ z, z ∉ L.lattice → 0 ≤ meromorphicOrderAt F z) →
      ((-(2 * k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F 0 →
      ∃ P : Polynomial ℂ, ∀ z : ℂ, F =ᶠ[𝓝[≠] z] fun w => P.eval (L.weierstrassP w) := by
  induction k with
  | zero =>
      intro F hmer hper _ hpol hord
      have hall : ∀ z : ℂ, 0 ≤ meromorphicOrderAt F z := by
        intro z
        by_cases hz : z ∈ L.lattice
        · have hshift := meromorphicOrderAt_add_period F z 0 (hper z hz)
          rw [zero_add] at hshift
          rw [hshift]
          simpa using hord
        · exact hpol z hz
      obtain ⟨c, hc⟩ := exists_const_eventuallyEq_of_lattice_periodic L hmer hper hall
      refine ⟨Polynomial.C c, fun z => ?_⟩
      filter_upwards [hc z] with w hw
      simpa using hw
  | succ k ih =>
      intro F hmer hper heven hpol hord
      by_cases hge : ((-(2 * k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt F 0
      · exact ih F hmer hper heven hpol hge
      rw [not_le] at hge
      have hnetop : meromorphicOrderAt F 0 ≠ ⊤ := by
        intro h
        rw [h] at hge
        exact absurd hge (by simp)
      lift meromorphicOrderAt F 0 to ℤ using hnetop with n hn
      have hnlt : n < -(2 * k : ℤ) := by exact_mod_cast hge
      have hnge : -(2 * ((k : ℤ) + 1)) ≤ n := by exact_mod_cast hord
      have hneven : Even n :=
        even_meromorphicOrderAt_of_neg_eq (hmer 0) heven hn.symm
      have hnval : n = -(2 * ((k : ℤ) + 1)) := by
        obtain ⟨m, hm⟩ := hneven
        omega
      set W : ℂ → ℂ := fun z => L.weierstrassP z ^ (k + 1) with hW
      have hWmer : ∀ z, MeromorphicAt W z := fun z => (L.meromorphic_weierstrassP z).pow _
      have hWord : meromorphicOrderAt W 0 = (n : WithTop ℤ) := by
        have h1 : meromorphicOrderAt W 0 = ((-(2 * ((k + 1 : ℕ) : ℤ)) : ℤ) : WithTop ℤ) :=
          meromorphicOrderAt_weierstrassP_pow_zero L (k + 1)
        have h2 : (-(2 * ((k + 1 : ℕ) : ℤ)) : ℤ) = n := by rw [hnval]; push_cast; ring
        rw [h1, h2]
      have htF : meromorphicTrailingCoeffAt F 0 ≠ 0 :=
        (hmer 0).meromorphicTrailingCoeffAt_ne_zero (by rw [← hn]; simp)
      have htW : meromorphicTrailingCoeffAt W 0 ≠ 0 :=
        (hWmer 0).meromorphicTrailingCoeffAt_ne_zero (by rw [hWord]; simp)
      set c : ℂ := meromorphicTrailingCoeffAt F 0 / meromorphicTrailingCoeffAt W 0 with hc
      have hc0 : c ≠ 0 := div_ne_zero htF htW
      set G : ℂ → ℂ := fun z => F z - c * W z with hG
      have hcWmer : ∀ z, MeromorphicAt (fun w => c * W w) z := fun z =>
        (MeromorphicAt.const c z).mul (hWmer z)
      have hcWord : ∀ z, meromorphicOrderAt (fun w => c * W w) z = meromorphicOrderAt W z := by
        intro z
        exact meromorphicOrderAt_smul_of_ne_zero (f := W) (g := fun _ : ℂ => c)
          analyticAt_const (by simpa using hc0)
      have hcWtrail : meromorphicTrailingCoeffAt (fun w => c * W w) 0
          = meromorphicTrailingCoeffAt F 0 := by
        rw [MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul
          (f₁ := fun _ : ℂ => c) (f₂ := W) (MeromorphicAt.const c 0) (hWmer 0),
          meromorphicTrailingCoeffAt_const, hc]
        field_simp
      have hGord0 : (n : WithTop ℤ) < meromorphicOrderAt G 0 := by
        have hlt := meromorphicOrderAt_lt_sub_of_trailingCoeff_eq (f := F) (g := fun w => c * W w)
          (x := 0) (hmer 0) (hcWmer 0)
          (by rw [← hn]; simp) (by rw [← hn, hcWord, hWord]) hcWtrail.symm
        rw [← hn] at hlt
        exact hlt
      have hGmer : ∀ z, MeromorphicAt G z := fun z => (hmer z).sub (hcWmer z)
      have hGper : ∀ p ∈ L.lattice, Function.Periodic G p := by
        intro p hp z
        simp only [hG, hW]
        rw [hper p hp z, weierstrassP_periodic L hp z]
      have hGeven : ∀ z, G (-z) = G z := by
        intro z
        simp only [hG, hW]
        rw [heven z, L.weierstrassP_neg z]
      have hGpol : ∀ z, z ∉ L.lattice → 0 ≤ meromorphicOrderAt G z := by
        intro z hz
        have hrw : G = F + fun w => -(c * W w) := by
          funext w
          simp [hG, sub_eq_add_neg]
        have hmin := meromorphicOrderAt_add (f₁ := F) (f₂ := fun w => -(c * W w)) (x := z)
          (hmer z) ((hcWmer z).neg)
        rw [← hrw] at hmin
        refine le_trans ?_ hmin
        refine le_min (hpol z hz) ?_
        have hnegord : meromorphicOrderAt (fun w => -(c * W w)) z
            = meromorphicOrderAt (fun w => c * W w) z := meromorphicOrderAt_fun_neg.symm
        rw [hnegord, hcWord z, hW]
        have hPan : AnalyticAt ℂ L.weierstrassP z := L.analyticOnNhd_weierstrassP z hz
        exact (hPan.fun_pow (k + 1)).meromorphicOrderAt_nonneg
      have hGbound : ((-(2 * k : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt G 0 := by
        rcases eq_or_ne (meromorphicOrderAt G 0) ⊤ with htop | htop
        · rw [htop]; exact le_top
        lift meromorphicOrderAt G 0 to ℤ using htop with m hm
        have hmgt : n < m := by exact_mod_cast hGord0
        have hmeven : Even m := even_meromorphicOrderAt_of_neg_eq (hGmer 0) hGeven hm.symm
        obtain ⟨j, hj⟩ := hmeven
        have hfin : -(2 * (k : ℤ)) ≤ m := by omega
        exact_mod_cast hfin
      obtain ⟨Q, hQ⟩ := ih G hGmer hGper hGeven hGpol hGbound
      refine ⟨Q + Polynomial.C c * Polynomial.X ^ (k + 1), fun z => ?_⟩
      filter_upwards [hQ z] with w hw
      have hFw : F w = G w + c * W w := by simp [hG]
      rw [hFw, hw]
      simp [hW]

/-- **Even elliptic functions with poles only on the lattice are polynomials in `℘`.**  No bound on
the pole order is assumed: one is produced from the order at the origin. -/
theorem exists_polynomial_eval_weierstrassP_of_even {F : ℂ → ℂ}
    (hmer : ∀ z, MeromorphicAt F z) (hper : ∀ p ∈ L.lattice, Function.Periodic F p)
    (heven : ∀ z, F (-z) = F z) (hpol : ∀ z, z ∉ L.lattice → 0 ≤ meromorphicOrderAt F z) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, F =ᶠ[𝓝[≠] z] fun w => P.eval (L.weierstrassP w) := by
  rcases eq_or_ne (meromorphicOrderAt F 0) ⊤ with htop | htop
  · refine exists_polynomial_eval_weierstrassP_of_orderBound L 0 F hmer hper heven hpol ?_
    rw [htop]
    exact le_top
  lift meromorphicOrderAt F 0 to ℤ using htop with n hn
  obtain ⟨k, hk⟩ : ∃ k : ℕ, -(2 * (k : ℤ)) ≤ n := ⟨(-n).toNat, by omega⟩
  refine exists_polynomial_eval_weierstrassP_of_orderBound L k F hmer hper heven hpol ?_
  rw [← hn]
  exact_mod_cast hk

end GaloisForLFunctions.HTGeometry
