import GaloisForLFunctions.HTGeometry.EllipticEvenPolynomialWeierstrass
import GaloisForLFunctions.HTGeometry.EllipticLatticeOrder

/-!
# Even elliptic functions are rational in `℘`

Every even meromorphic function invariant under a period lattice is a rational function of the
Weierstrass `℘` of that lattice.

The poles of such a function outside the lattice are finitely many modulo the lattice, and every one
of them is congruent to a pole inside the fundamental parallelogram.  Multiplying by the
corresponding product of factors `℘ - ℘(a)`, each raised to the pole order at `a`, clears every pole
off the lattice, because `℘` is lattice-periodic, so `℘ - ℘(a)` vanishes at the whole class of `a`.
The product is even and lattice-periodic, so the cleared function is a polynomial in `℘`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable (L : PeriodPair)

/-- An analytic function vanishing at a point has order at least one there. -/
theorem one_le_meromorphicOrderAt_of_analyticAt_eq_zero {h : ℂ → ℂ} {z : ℂ}
    (hh : AnalyticAt ℂ h z) (hz : h z = 0) : (1 : WithTop ℤ) ≤ meromorphicOrderAt h z := by
  rw [hh.meromorphicOrderAt_eq]
  have hne0 : analyticOrderAt h z ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    simp only [not_or, not_not]
    exact ⟨hh, hz⟩
  have h1 : (1 : ℕ∞) ≤ analyticOrderAt h z := Order.one_le_iff_ne_zero.mpr hne0
  have hmono : Monotone (ENat.map (Nat.cast : ℕ → ℤ)) := ENat.monotone_map_iff.mpr Nat.mono_cast
  simpa using hmono h1

/-- A power of an analytic function vanishing at a point has order at least the exponent. -/
theorem le_meromorphicOrderAt_pow_of_analyticAt_eq_zero {h : ℂ → ℂ} {z : ℂ}
    (hh : AnalyticAt ℂ h z) (hz : h z = 0) (m : ℕ) :
    ((m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (fun w => h w ^ m) z := by
  induction m with
  | zero =>
      have hfun : (fun w : ℂ => h w ^ 0) = fun _ : ℂ => (1 : ℂ) := by funext w; simp
      have hord0 : analyticOrderAt (fun _ : ℂ => (1 : ℂ)) z = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr one_ne_zero)
      rw [hfun, (analyticAt_const (v := (1 : ℂ)) (x := z)).meromorphicOrderAt_eq, hord0]
      simp
  | succ m ih =>
      have hsplit : (fun w : ℂ => h w ^ (m + 1)) = fun w : ℂ => (h w ^ m) * h w := by
        funext w; ring
      rw [hsplit, fun_meromorphicOrderAt_mul (f := fun w : ℂ => h w ^ m) (g := h)
        ((hh.meromorphicAt).pow m) hh.meromorphicAt]
      have hcast : (((m + 1 : ℕ) : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) + 1 := by
        push_cast
        rfl
      rw [hcast]
      exact add_le_add ih (one_le_meromorphicOrderAt_of_analyticAt_eq_zero hh hz)

section

variable {f : ℂ → ℂ} (hmer : ∀ z, MeromorphicAt f z)
  (hper : ∀ p ∈ L.lattice, Function.Periodic f p)

include hmer in
/-- The meromorphic hypothesis in the form the pole-finiteness lemma consumes. -/
theorem meromorphicOn_univ_of_forall : MeromorphicOn f Set.univ := fun z _ => hmer z

include hmer hper in
/-- **Every pole is congruent to a pole of the fundamental parallelogram**, with the same order and
the same value of `℘`. -/
theorem exists_pole_representative_weierstrassP {z : ℂ}
    (hz : meromorphicOrderAt f z < 0) :
    ∃ p ∈ (finite_poles_fundamentalParallelogram (meromorphicOn_univ_of_forall hmer)
        L.ω₁ L.ω₂).toFinset,
      L.weierstrassP p = L.weierstrassP z ∧ meromorphicOrderAt f p = meromorphicOrderAt f z := by
  obtain ⟨_, _, hcov⟩ := exists_bounded_intCombination L.indep
  obtain ⟨m, n, hmem, _, _⟩ := hcov z
  have hlat : m • L.ω₁ + n • L.ω₂ ∈ L.lattice := by
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact L.ω₁_mem_lattice
    · exact L.ω₂_mem_lattice
  have hord : meromorphicOrderAt f (z - (m • L.ω₁ + n • L.ω₂)) = meromorphicOrderAt f z :=
    meromorphicOrderAt_sub_latticeCombination (hper L.ω₁ L.ω₁_mem_lattice)
      (hper L.ω₂ L.ω₂_mem_lattice) m n z
  refine ⟨z - (m • L.ω₁ + n • L.ω₂), ?_, ?_, hord⟩
  · rw [Set.Finite.mem_toFinset]
    exact ⟨hmem, by rw [hord]; exact hz⟩
  · exact L.weierstrassP_sub_coe z ⟨_, hlat⟩

end

section

variable {f : ℂ → ℂ} (hmer : ∀ z, MeromorphicAt f z)
  (hper : ∀ p ∈ L.lattice, Function.Periodic f p) (heven : ∀ z, f (-z) = f z)

/-- The pole order of `f` at a point, as a natural number. -/
noncomputable def poleOrder (f : ℂ → ℂ) (a : ℂ) : ℕ := (-(meromorphicOrderAt f a).untop₀).toNat

include hmer hper heven in
/-- **Even elliptic functions are rational in `℘`.**  The clearing denominator is the monic product
of the factors `X - ℘(a)` over the poles `a` in the fundamental parallelogram, each raised to the
pole order at `a`. -/
theorem exists_rational_eval_weierstrassP_of_even :
    ∃ P Q : Polynomial ℂ, Q.Monic ∧
      ∀ z : ℂ, (fun w => f w * Q.eval (L.weierstrassP w)) =ᶠ[𝓝[≠] z]
        fun w => P.eval (L.weierstrassP w) := by
  classical
  set S : Finset ℂ :=
    (finite_poles_fundamentalParallelogram (meromorphicOn_univ_of_forall hmer) L.ω₁ L.ω₂).toFinset
      with hS
  set Q : Polynomial ℂ :=
    ∏ a ∈ S, (Polynomial.X - Polynomial.C (L.weierstrassP a)) ^ poleOrder f a with hQ
  have hQmonic : Q.Monic := by
    refine Polynomial.monic_prod_of_monic _ _ fun a _ => ?_
    exact (Polynomial.monic_X_sub_C (L.weierstrassP a)).pow _
  set D : ℂ → ℂ :=
    fun w => ∏ a ∈ S, (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a with hD
  have hDeval : ∀ w : ℂ, Q.eval (L.weierstrassP w) = D w := by
    intro w
    rw [hQ, hD, Polynomial.eval_prod]
    exact Finset.prod_congr rfl fun a _ => by simp
  set F : ℂ → ℂ := fun w => f w * D w with hF
  have hfacMer : ∀ (a : ℂ) (z : ℂ),
      MeromorphicAt (fun w => (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a) z := by
    intro a z
    exact (((L.meromorphic_weierstrassP z).sub (MeromorphicAt.const _ z))).pow _
  have hDmer : ∀ z, MeromorphicAt D z := by
    intro z
    exact MeromorphicAt.fun_prod fun a _ => hfacMer a z
  have hFmer : ∀ z, MeromorphicAt F z := fun z => (hmer z).mul (hDmer z)
  have hDper : ∀ p ∈ L.lattice, Function.Periodic D p := by
    intro p hp w
    simp only [hD]
    exact Finset.prod_congr rfl fun a _ => by rw [weierstrassP_periodic L hp w]
  have hFper : ∀ p ∈ L.lattice, Function.Periodic F p := by
    intro p hp w
    simp only [hF]
    rw [hper p hp w, hDper p hp w]
  have hDeven : ∀ w : ℂ, D (-w) = D w := by
    intro w
    simp only [hD]
    exact Finset.prod_congr rfl fun a _ => by rw [L.weierstrassP_neg w]
  have hFeven : ∀ w : ℂ, F (-w) = F w := by
    intro w
    simp only [hF]
    rw [heven w, hDeven w]
  have hFpol : ∀ z, z ∉ L.lattice → 0 ≤ meromorphicOrderAt F z := by
    intro z hz
    have hPan : AnalyticAt ℂ L.weierstrassP z := L.analyticOnNhd_weierstrassP z hz
    have hfacAn : ∀ a : ℂ, AnalyticAt ℂ (fun w => L.weierstrassP w - L.weierstrassP a) z :=
      fun a => hPan.fun_sub analyticAt_const
    have hDord : meromorphicOrderAt D z
        = ∑ a ∈ S, meromorphicOrderAt
            (fun w => (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a) z := by
      rw [hD]
      exact meromorphicOrderAt_fun_prod fun a _ => hfacMer a z
    have hnonneg : ∀ a ∈ S, 0 ≤ meromorphicOrderAt
        (fun w => (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a) z :=
      fun a _ => ((hfacAn a).fun_pow _).meromorphicOrderAt_nonneg
    rw [hF, fun_meromorphicOrderAt_mul (hmer z) (hDmer z), hDord]
    rcases lt_or_ge (meromorphicOrderAt f z) 0 with hlt | hge
    · obtain ⟨p, hpS, hpP, hpord⟩ :=
        exists_pole_representative_weierstrassP L hmer hper hlt
      rw [← hS] at hpS
      have hvan : (fun w => L.weierstrassP w - L.weierstrassP p) z = 0 := by
        simp [hpP]
      have hple : ((poleOrder f p : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
          (fun w => (L.weierstrassP w - L.weierstrassP p) ^ poleOrder f p) z :=
        le_meromorphicOrderAt_pow_of_analyticAt_eq_zero (hfacAn p) hvan _
      have hsplit : ∑ a ∈ S, meromorphicOrderAt
            (fun w => (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a) z
          = meromorphicOrderAt
              (fun w => (L.weierstrassP w - L.weierstrassP p) ^ poleOrder f p) z
            + ∑ a ∈ S.erase p, meromorphicOrderAt
              (fun w => (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a) z :=
        (Finset.add_sum_erase S _ hpS).symm
      rw [hsplit]
      have hrest : (0 : WithTop ℤ) ≤ ∑ a ∈ S.erase p, meromorphicOrderAt
          (fun w => (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a) z :=
        Finset.sum_nonneg fun a ha => hnonneg a (Finset.mem_of_mem_erase ha)
      have hnetop : meromorphicOrderAt f z ≠ ⊤ := ne_top_of_lt hlt
      lift meromorphicOrderAt f z to ℤ using hnetop with n hn
      have hpn : meromorphicOrderAt f p = (n : WithTop ℤ) := hpord
      have hpoleval : ((poleOrder f p : ℤ)) = -n := by
        rw [poleOrder, hpn]
        have hnlt : n < 0 := by exact_mod_cast hlt
        simp only [WithTop.untop₀_coe]
        omega
      have hkey : (0 : WithTop ℤ) ≤ (n : WithTop ℤ) + ((poleOrder f p : ℤ) : WithTop ℤ) := by
        rw [hpoleval]
        rw [← WithTop.coe_add]
        simp
      calc (0 : WithTop ℤ) ≤ (n : WithTop ℤ) + ((poleOrder f p : ℤ) : WithTop ℤ) := hkey
        _ ≤ (n : WithTop ℤ) + meromorphicOrderAt
              (fun w => (L.weierstrassP w - L.weierstrassP p) ^ poleOrder f p) z := by gcongr
        _ ≤ (n : WithTop ℤ) + (meromorphicOrderAt
              (fun w => (L.weierstrassP w - L.weierstrassP p) ^ poleOrder f p) z
            + ∑ a ∈ S.erase p, meromorphicOrderAt
              (fun w => (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a) z) := by
            gcongr
            exact le_add_of_nonneg_right hrest
    · have hsum : (0 : WithTop ℤ) ≤ ∑ a ∈ S, meromorphicOrderAt
          (fun w => (L.weierstrassP w - L.weierstrassP a) ^ poleOrder f a) z :=
        Finset.sum_nonneg hnonneg
      exact add_nonneg hge hsum
  obtain ⟨P, hP⟩ :=
    exists_polynomial_eval_weierstrassP_of_even L hFmer hFper hFeven hFpol
  refine ⟨P, Q, hQmonic, fun z => ?_⟩
  filter_upwards [hP z] with w hw
  rw [hDeval w]
  exact hw

end

end GaloisForLFunctions.HTGeometry
