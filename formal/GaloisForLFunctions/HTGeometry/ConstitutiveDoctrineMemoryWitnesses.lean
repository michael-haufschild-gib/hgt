import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum
import GaloisForLFunctions.HTGeometry.DifferentialOrder
import GaloisForLFunctions.HTGeometry.AnalyticJetOrderBridge
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence

/-!
# Witnesses of the doctrine-relative memory spectrum

The constant-response doctrine, the base-aware linear doctrine and the algebraic differential
doctrine are strictly separated by three germs.  `exp (z²)` has infinite Hankel memory yet a single
linear state; `tan` has no finite linear memory yet an order-one algebraic relation; the shifted
Gamma germ has no algebraic differential relation at all.  Base-aware linear memory is developed
here as the `ℂ(z)`-span of the jets, cleared of denominators.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset
open scoped Matrix

/-! ## §4.1 — infinite constant memory with one linear state: `exp (z²)` -/

section GaussianWitness

open Filter Topology

/-- The Gaussian germ. -/
noncomputable def expSq (z : ℂ) : ℂ := Complex.exp (z ^ (2 : ℕ))

/-- The Hermite-type polynomial coefficients of the jets of `exp (z²)`. -/
noncomputable def gaussianJetPoly : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => Polynomial.derivative (gaussianJetPoly n) + 2 * Polynomial.X * gaussianJetPoly n

theorem hasDerivAt_expSq (z : ℂ) : HasDerivAt expSq (2 * z * expSq z) z := by
  have h : HasDerivAt (fun w : ℂ => Complex.exp (w ^ (2 : ℕ)))
      (Complex.exp (z ^ (2 : ℕ)) * (2 * z ^ (1 : ℕ))) z := by
    simpa using (hasDerivAt_pow 2 z).cexp
  have hmul : Complex.exp (z ^ (2 : ℕ)) * (2 * z ^ (1 : ℕ)) = 2 * z * expSq z := by
    rw [expSq, pow_one]
    ring
  rwa [hmul] at h

/-- Every jet of `exp (z²)` is a polynomial multiple of `exp (z²)`. -/
theorem iteratedDeriv_expSq (n : ℕ) :
    iteratedDeriv n expSq = fun z => (gaussianJetPoly n).eval z * expSq z := by
  induction n with
  | zero =>
    funext z
    rw [iteratedDeriv_zero, gaussianJetPoly]
    simp
  | succ n ih =>
    funext z
    rw [iteratedDeriv_succ, ih]
    have hd : HasDerivAt (fun w : ℂ => (gaussianJetPoly n).eval w * expSq w)
        ((Polynomial.derivative (gaussianJetPoly n)).eval z * expSq z
          + (gaussianJetPoly n).eval z * (2 * z * expSq z)) z :=
      ((gaussianJetPoly n).hasDerivAt z).mul (hasDerivAt_expSq z)
    rw [hd.deriv, gaussianJetPoly]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
    ring

theorem natDegree_hermitePoly_le (n : ℕ) : (gaussianJetPoly n).natDegree ≤ n := by
  induction n with
  | zero => simp [gaussianJetPoly]
  | succ n ih =>
    rw [gaussianJetPoly]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · have h : (Polynomial.derivative (gaussianJetPoly n)).natDegree
          ≤ (gaussianJetPoly n).natDegree - 1 := Polynomial.natDegree_derivative_le _
      omega
    · refine (Polynomial.natDegree_mul_le).trans ?_
      have h2 : ((2 : Polynomial ℂ) * Polynomial.X).natDegree ≤ 1 :=
        Polynomial.natDegree_mul_le.trans (by simp)
      omega

theorem coeff_hermitePoly_self (n : ℕ) : (gaussianJetPoly n).coeff n = 2 ^ n := by
  induction n with
  | zero => simp [gaussianJetPoly]
  | succ n ih =>
    rw [gaussianJetPoly, Polynomial.coeff_add]
    have hderiv : (Polynomial.derivative (gaussianJetPoly n)).coeff (n + 1) = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have h1 : (Polynomial.derivative (gaussianJetPoly n)).natDegree
          ≤ (gaussianJetPoly n).natDegree - 1 := Polynomial.natDegree_derivative_le _
      have h2 := natDegree_hermitePoly_le n
      omega
    have hmul : ((2 : Polynomial ℂ) * Polynomial.X * gaussianJetPoly n).coeff (n + 1)
        = 2 * (gaussianJetPoly n).coeff n := by
      rw [mul_assoc, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_mul]
    rw [hderiv, hmul, ih, zero_add, pow_succ]
    ring

/-- **Equation (10), first component.**  `exp (z²)` satisfies no constant-coefficient linear
differential equation: the induced polynomial identity has a nonzero leading coefficient. -/
theorem not_germConstantODE_expSq : ¬ GermConstantODE expSq := by
  rintro ⟨p, hp, hode⟩
  set Q : Polynomial ℂ := ∑ k ∈ Finset.range (p.natDegree + 1),
    Polynomial.C (p.coeff k) * gaussianJetPoly k with hQ
  have hQcoeff : Q.coeff p.natDegree = p.coeff p.natDegree * 2 ^ p.natDegree := by
    rw [hQ, Polynomial.finsetSum_coeff, Finset.sum_eq_single p.natDegree]
    · rw [Polynomial.coeff_C_mul, coeff_hermitePoly_self]
    · intro k hk hkne
      have hklt : k < p.natDegree := by
        have := Finset.mem_range.mp hk
        omega
      have hz : (gaussianJetPoly k).coeff p.natDegree = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (natDegree_hermitePoly_le k) hklt)
      rw [Polynomial.coeff_C_mul, hz, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  have hQne : Q ≠ 0 := by
    intro h0
    have hlead : p.coeff p.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    rw [h0, Polynomial.coeff_zero] at hQcoeff
    exact (mul_ne_zero hlead (pow_ne_zero _ two_ne_zero)) hQcoeff.symm
  -- the equation forces `Q` to vanish on a neighbourhood of the origin
  have hvanish : ∀ᶠ z in 𝓝 (0 : ℂ), Q.eval z = 0 := by
    filter_upwards [hode] with z hz
    have hexp : expSq z ≠ 0 := Complex.exp_ne_zero _
    have hsum : (∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k * (gaussianJetPoly k).eval z) * expSq z = 0 := by
      rw [Finset.sum_mul, ← hz]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [iteratedDeriv_expSq k]
      ring
    have hzero : ∑ k ∈ Finset.range (p.natDegree + 1),
        p.coeff k * (gaussianJetPoly k).eval z = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact h
      · exact absurd h hexp
    rw [hQ, Polynomial.eval_finsetSum]
    rw [← hzero]
    exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.eval_mul, Polynomial.eval_C]
  -- a polynomial vanishing on a neighbourhood has infinitely many roots
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hvanish
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hinj : Function.Injective fun n : ℕ => ((ε / ((n : ℝ) + 2) : ℝ) : ℂ) := by
    intro a b hab
    have h1 : (ε / ((a : ℝ) + 2)) = (ε / ((b : ℝ) + 2)) := Complex.ofReal_inj.mp hab
    have ha : (0 : ℝ) < (a : ℝ) + 2 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 2 := by positivity
    rw [div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)] at h1
    have h2 : (a : ℝ) = (b : ℝ) := by
      have := mul_left_cancel₀ hεne (by linarith : ε * ((b : ℝ) + 2) = ε * ((a : ℝ) + 2))
      linarith
    exact_mod_cast h2
  have hmem : ∀ n : ℕ, ((ε / ((n : ℝ) + 2) : ℝ) : ℂ) ∈ {z : ℂ | Q.IsRoot z} := by
    intro n
    have hlt : ε / ((n : ℝ) + 2) < ε := by
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      rw [div_lt_iff₀ hpos]
      nlinarith
    have hnn : (0 : ℝ) ≤ ε / ((n : ℝ) + 2) := by positivity
    have hdist : dist (((ε / ((n : ℝ) + 2)) : ℝ) : ℂ) 0 < ε := by
      rw [Complex.dist_eq, sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hlt
    exact hball hdist
  exact hQne (Polynomial.eq_zero_of_infinite_isRoot Q
    (Set.infinite_of_injective_forall_mem hinj hmem))

/-- **Equation (10), first component.**  The constant-response memory of `exp (z²)` is infinite. -/
theorem not_bddHankelRank_expSq : ¬ BddHankelRank (respSeq expSq) := by
  intro h
  have hana : AnalyticAt ℂ expSq 0 := by
    have : AnalyticAt ℂ (fun z : ℂ => z ^ (2 : ℕ)) 0 := (analyticAt_id.pow 2)
    exact this.cexp
  exact not_germConstantODE_expSq
    ((seqConstantRecurrence_respSeq_iff_germConstantODE hana).mp
      (seqConstantRecurrence_of_bddHankelRank h))

/-- **Equation (10), third component.**  `exp (z²)` satisfies the order-one algebraic differential
equation `f' = 2 z f`, so its algebraic intervention profile is constant. -/
theorem differentiallyAlgebraicOfOrder_expSq :
    GaloisForLFunctions.DifferentiallyAlgebraicOfOrder expSq 1 := by
  refine ⟨MvPolynomial.X 2 - 2 * MvPolynomial.X 0 * MvPolynomial.X 1, ?_, ?_⟩
  · intro h0
    have hev := congrArg
      (MvPolynomial.eval (fun i : Fin 3 => if i = 2 then (1 : ℂ) else 0)) h0
    simp at hev
  · intro z
    have hd : iteratedDeriv 1 expSq z = 2 * z * expSq z := by
      rw [iteratedDeriv_one]
      exact (hasDerivAt_expSq z).deriv
    have h0 : iteratedDeriv 0 expSq z = expSq z := by rw [iteratedDeriv_zero]
    simp only [map_sub, map_mul, MvPolynomial.eval_X, map_ofNat]
    have hc0 : ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) expSq z : Fin 3 → ℂ)) 0 = z := by simp
    have hc1 : ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) expSq z : Fin 3 → ℂ)) 1
        = iteratedDeriv 0 expSq z := by
      show ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) expSq z : Fin 3 → ℂ)) (Fin.succ 0) = _
      rw [Fin.cons_succ]
      norm_num
    have hc2 : ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) expSq z : Fin 3 → ℂ)) 2
        = iteratedDeriv 1 expSq z := by
      show ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) expSq z : Fin 3 → ℂ)) (Fin.succ 1) = _
      rw [Fin.cons_succ]
      norm_num
    rw [hc0, hc1, hc2, hd, h0]
    ring

end GaussianWitness

/-! ## §3 — base-aware linear memory -/

section LinearMemory

open Filter Topology

/-- Membership in the `ℂ(z)`-span of the first `n` jets of `f` on `U`, cleared of denominators. -/
def InJetSpan (f : ℂ → ℂ) (U : Set ℂ) (n : ℕ) (g : ℂ → ℂ) : Prop :=
  ∃ (c : ℕ → Polynomial ℂ) (d : Polynomial ℂ), d ≠ 0 ∧
    ∀ z ∈ U, d.eval z * g z = ∑ i ∈ Finset.range n, (c i).eval z * iteratedDeriv i f z

/-- **Equation (3).**  The base-aware linear memory of `f` is at most `n`. -/
def LinearMemoryAtMost (f : ℂ → ℂ) (U : Set ℂ) (n : ℕ) : Prop :=
  ∀ N : ℕ, InJetSpan f U n (iteratedDeriv N f)

/-- A nonzero linear differential equation with polynomial coefficients on `U`. -/
def DFiniteOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ (n : ℕ) (c : ℕ → Polynomial ℂ), c n ≠ 0 ∧
    ∀ z ∈ U, ∑ i ∈ Finset.range (n + 1), (c i).eval z * iteratedDeriv i f z = 0

theorem InJetSpan.congr {f g₁ g₂ : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (h : InJetSpan f U n g₁) (heq : ∀ z ∈ U, g₁ z = g₂ z) : InJetSpan f U n g₂ := by
  obtain ⟨c, d, hd, hrel⟩ := h
  exact ⟨c, d, hd, fun z hz => by rw [← heq z hz]; exact hrel z hz⟩

theorem inJetSpan_zero (f : ℂ → ℂ) (U : Set ℂ) (n : ℕ) : InJetSpan f U n (fun _ => 0) :=
  ⟨fun _ => 0, 1, one_ne_zero, fun z _ => by simp⟩

theorem InJetSpan.add {f g₁ g₂ : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (h₁ : InJetSpan f U n g₁) (h₂ : InJetSpan f U n g₂) :
    InJetSpan f U n (fun z => g₁ z + g₂ z) := by
  obtain ⟨c₁, d₁, hd₁, hrel₁⟩ := h₁
  obtain ⟨c₂, d₂, hd₂, hrel₂⟩ := h₂
  refine ⟨fun i => d₂ * c₁ i + d₁ * c₂ i, d₁ * d₂, mul_ne_zero hd₁ hd₂, fun z hz => ?_⟩
  have h1 := hrel₁ z hz
  have h2 := hrel₂ z hz
  rw [Polynomial.eval_mul]
  calc d₁.eval z * d₂.eval z * (g₁ z + g₂ z)
      = d₂.eval z * (d₁.eval z * g₁ z) + d₁.eval z * (d₂.eval z * g₂ z) := by ring
    _ = d₂.eval z * (∑ i ∈ Finset.range n, (c₁ i).eval z * iteratedDeriv i f z)
        + d₁.eval z * (∑ i ∈ Finset.range n, (c₂ i).eval z * iteratedDeriv i f z) := by
          rw [h1, h2]
    _ = ∑ i ∈ Finset.range n, ((d₂ * c₁ i + d₁ * c₂ i).eval z * iteratedDeriv i f z) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]
          ring

theorem InJetSpan.polyMul {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ} (h : InJetSpan f U n g)
    (P : Polynomial ℂ) : InJetSpan f U n (fun z => P.eval z * g z) := by
  obtain ⟨c, d, hd, hrel⟩ := h
  refine ⟨fun i => P * c i, d, hd, fun z hz => ?_⟩
  calc d.eval z * (P.eval z * g z) = P.eval z * (d.eval z * g z) := by ring
    _ = P.eval z * ∑ i ∈ Finset.range n, (c i).eval z * iteratedDeriv i f z := by rw [hrel z hz]
    _ = ∑ i ∈ Finset.range n, ((P * c i).eval z * iteratedDeriv i f z) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.eval_mul]
        ring

theorem InJetSpan.polyDiv {f g : ℂ → ℂ} {U : Set ℂ} {n : ℕ} {P : Polynomial ℂ} (hP : P ≠ 0)
    (h : InJetSpan f U n fun z => P.eval z * g z) : InJetSpan f U n g := by
  obtain ⟨c, d, hd, hrel⟩ := h
  refine ⟨c, d * P, mul_ne_zero hd hP, fun z hz => ?_⟩
  rw [Polynomial.eval_mul]
  calc d.eval z * P.eval z * g z = d.eval z * (P.eval z * g z) := by ring
    _ = ∑ i ∈ Finset.range n, (c i).eval z * iteratedDeriv i f z := hrel z hz

theorem InJetSpan.sum {f : ℂ → ℂ} {U : Set ℂ} {n : ℕ} {s : Finset ℕ} {g : ℕ → ℂ → ℂ}
    (h : ∀ i ∈ s, InJetSpan f U n (g i)) : InJetSpan f U n (fun z => ∑ i ∈ s, g i z) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using inJetSpan_zero f U n
  | insert a s ha ih =>
    have hmem : InJetSpan f U n (g a) := h a (Finset.mem_insert_self a s)
    have hrest : InJetSpan f U n (fun z => ∑ i ∈ s, g i z) :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine (hmem.add hrest).congr fun z _ => ?_
    rw [Finset.sum_insert ha]

theorem inJetSpan_iteratedDeriv_of_lt (f : ℂ → ℂ) (U : Set ℂ) {n i : ℕ} (hi : i < n) :
    InJetSpan f U n (iteratedDeriv i f) := by
  classical
  refine ⟨fun j => if j = i then 1 else 0, 1, one_ne_zero, fun z _ => ?_⟩
  rw [Polynomial.eval_one, one_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro hmem
    exact absurd (Finset.mem_range.mpr hi) hmem

/-- The top jet of a `D`-finite germ lies in the span of the lower ones. -/
theorem inJetSpan_top_of_dFiniteOn {f : ℂ → ℂ} {U : Set ℂ} {n : ℕ} {c : ℕ → Polynomial ℂ}
    (hc : c n ≠ 0)
    (hrel : ∀ z ∈ U, ∑ i ∈ Finset.range (n + 1), (c i).eval z * iteratedDeriv i f z = 0) :
    InJetSpan f U n (iteratedDeriv n f) := by
  refine ⟨fun i => -c i, c n, hc, fun z hz => ?_⟩
  have h := hrel z hz
  rw [Finset.sum_range_succ] at h
  calc (c n).eval z * iteratedDeriv n f z
      = -∑ i ∈ Finset.range n, (c i).eval z * iteratedDeriv i f z := by linear_combination h
    _ = ∑ i ∈ Finset.range n, ((-c i).eval z * iteratedDeriv i f z) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.eval_neg]
        ring

theorem inJetSpan_iteratedDeriv_of_le {f : ℂ → ℂ} {U : Set ℂ} {n : ℕ} {c : ℕ → Polynomial ℂ}
    (hc : c n ≠ 0)
    (hrel : ∀ z ∈ U, ∑ i ∈ Finset.range (n + 1), (c i).eval z * iteratedDeriv i f z = 0)
    {i : ℕ} (hi : i ≤ n) : InJetSpan f U n (iteratedDeriv i f) := by
  rcases lt_or_eq_of_le hi with h | h
  · exact inJetSpan_iteratedDeriv_of_lt f U h
  · subst h
    exact inJetSpan_top_of_dFiniteOn hc hrel

/-- **The span of the first `n` jets is closed under differentiation** once the germ satisfies a
linear differential equation of order `n`. -/
theorem InJetSpan.deriv_mem {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z) {n : ℕ} {b : ℕ → Polynomial ℂ} (hb : b n ≠ 0)
    (hODE : ∀ z ∈ U, ∑ i ∈ Finset.range (n + 1), (b i).eval z * iteratedDeriv i f z = 0)
    {g : ℂ → ℂ} (hgd : ∀ z ∈ U, DifferentiableAt ℂ g z) (hg : InJetSpan f U n g) :
    InJetSpan f U n (deriv g) := by
  obtain ⟨c, d, hd, hrel⟩ := hg
  -- differentiate the cleared identity on the open set `U`
  have hderiv : ∀ z ∈ U, (Polynomial.derivative d).eval z * g z + d.eval z * deriv g z
      = ∑ i ∈ Finset.range n, ((Polynomial.derivative (c i)).eval z * iteratedDeriv i f z
        + (c i).eval z * iteratedDeriv (i + 1) f z) := by
    intro z hz
    have hev : (fun w => d.eval w * g w) =ᶠ[𝓝 z]
        fun w => ∑ i ∈ Finset.range n, (c i).eval w * iteratedDeriv i f w := by
      filter_upwards [hU.mem_nhds hz] with w hw using hrel w hw
    have hL : HasDerivAt (fun w => d.eval w * g w)
        ((Polynomial.derivative d).eval z * g z + d.eval z * deriv g z) z :=
      (d.hasDerivAt z).mul ((hgd z hz).hasDerivAt)
    have hR : HasDerivAt (fun w => ∑ i ∈ Finset.range n, (c i).eval w * iteratedDeriv i f w)
        (∑ i ∈ Finset.range n, ((Polynomial.derivative (c i)).eval z * iteratedDeriv i f z
          + (c i).eval z * iteratedDeriv (i + 1) f z)) z := by
      refine HasDerivAt.fun_sum fun i _ => ?_
      have hi : HasDerivAt (fun w => iteratedDeriv i f w) (iteratedDeriv (i + 1) f z) z := by
        have := (analyticAt_iteratedDeriv (hf z hz) i).differentiableAt.hasDerivAt
        rw [iteratedDeriv_succ]
        exact this
      exact ((c i).hasDerivAt z).mul hi
    have := hev.deriv_eq
    rw [hL.deriv, hR.deriv] at this
    exact this
  -- clear the new denominator
  have hkey : InJetSpan f U n fun z => (d ^ (2 : ℕ)).eval z * deriv g z := by
    have hpieces : InJetSpan f U n fun z =>
        d.eval z * (∑ i ∈ Finset.range n, ((Polynomial.derivative (c i)).eval z
            * iteratedDeriv i f z + (c i).eval z * iteratedDeriv (i + 1) f z))
          - (Polynomial.derivative d).eval z
            * (∑ i ∈ Finset.range n, (c i).eval z * iteratedDeriv i f z) := by
      have hsum1 : InJetSpan f U n fun z => ∑ i ∈ Finset.range n,
          ((Polynomial.derivative (c i)).eval z * iteratedDeriv i f z
            + (c i).eval z * iteratedDeriv (i + 1) f z) := by
        refine InJetSpan.sum fun i hi => ?_
        have hin : i < n := Finset.mem_range.mp hi
        have h1 : InJetSpan f U n fun z =>
            (Polynomial.derivative (c i)).eval z * iteratedDeriv i f z :=
          (inJetSpan_iteratedDeriv_of_lt f U hin).polyMul _
        have h2 : InJetSpan f U n fun z => (c i).eval z * iteratedDeriv (i + 1) f z :=
          (inJetSpan_iteratedDeriv_of_le hb hODE (by omega)).polyMul _
        exact h1.add h2
      have hsum2 : InJetSpan f U n fun z =>
          ∑ i ∈ Finset.range n, (c i).eval z * iteratedDeriv i f z := by
        refine InJetSpan.sum fun i hi => ?_
        exact (inJetSpan_iteratedDeriv_of_lt f U (Finset.mem_range.mp hi)).polyMul _
      have hA := hsum1.polyMul d
      have hB := (hsum2.polyMul (Polynomial.derivative d)).polyMul (-1 : Polynomial ℂ)
      refine (hA.add hB).congr fun z _ => ?_
      simp only [Polynomial.eval_neg, Polynomial.eval_one]
      ring
    refine hpieces.congr fun z hz => ?_
    have h1 := hderiv z hz
    have h2 := hrel z hz
    have hd2 : (d ^ (2 : ℕ)).eval z = d.eval z * d.eval z := by
      rw [Polynomial.eval_pow]; ring
    rw [hd2]
    linear_combination (Polynomial.derivative d).eval z * h2 - d.eval z * h1
  exact hkey.polyDiv (pow_ne_zero 2 hd)

/-- **Theorem 3.1, clause 1, one direction.**  A nonzero linear differential equation gives finite
base-aware linear memory. -/
theorem linearMemoryAtMost_of_dFiniteOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z) {n : ℕ} {b : ℕ → Polynomial ℂ} (hb : b n ≠ 0)
    (hODE : ∀ z ∈ U, ∑ i ∈ Finset.range (n + 1), (b i).eval z * iteratedDeriv i f z = 0) :
    LinearMemoryAtMost f U n := by
  intro N
  induction N with
  | zero =>
    have h := inJetSpan_iteratedDeriv_of_le hb hODE (Nat.zero_le n)
    exact h
  | succ N ih =>
    have hgd : ∀ z ∈ U, DifferentiableAt ℂ (iteratedDeriv N f) z := fun z hz =>
      (analyticAt_iteratedDeriv (hf z hz) N).differentiableAt
    have := InJetSpan.deriv_mem hU hf hb hODE hgd ih
    rw [iteratedDeriv_succ]
    exact this

/-- **Theorem 3.1, clause 1, converse.**  Finite base-aware linear memory is a nonzero linear
differential equation. -/
theorem dFiniteOn_of_linearMemoryAtMost {f : ℂ → ℂ} {U : Set ℂ} {n : ℕ}
    (h : LinearMemoryAtMost f U n) : DFiniteOn f U := by
  obtain ⟨c, d, hd, hrel⟩ := h n
  classical
  refine ⟨n, fun i => if i = n then d else -c i, ?_, fun z hz => ?_⟩
  · simpa using hd
  · rw [Finset.sum_range_succ]
    have hlast : (if n = n then d else -c n).eval z * iteratedDeriv n f z
        = d.eval z * iteratedDeriv n f z := by rw [if_pos rfl]
    have hearly : ∑ i ∈ Finset.range n,
        (if i = n then d else -c i).eval z * iteratedDeriv i f z
          = -∑ i ∈ Finset.range n, (c i).eval z * iteratedDeriv i f z := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≠ n := by
        have := Finset.mem_range.mp hi
        omega
      rw [if_neg hin, Polynomial.eval_neg]
      ring
    rw [hlast, hearly]
    linear_combination hrel z hz

/-- **Theorem 3.1, clause 1.**  Finite base-aware linear memory and `D`-finiteness are the same
condition. -/
theorem linearMemory_iff_dFiniteOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z) :
    (∃ n, LinearMemoryAtMost f U n) ↔ DFiniteOn f U := by
  constructor
  · rintro ⟨n, h⟩
    exact dFiniteOn_of_linearMemoryAtMost h
  · rintro ⟨n, b, hb, hODE⟩
    exact ⟨n, linearMemoryAtMost_of_dFiniteOn hU hf hb hODE⟩

end LinearMemory

/-! ## §3, clauses 2 and 3 — algebraic intervention memory -/

section AlgebraicMemory

open GaloisForLFunctions Bottcher

/-- **Theorem 3.1, clause 2.**  Differential algebraicity is exactly a finite bound on the
algebraic intervention profile: some finite jet already carries a relation. -/
theorem differentiallyAlgebraic_iff_exists_order' (g : ℂ → ℂ) :
    DifferentiallyAlgebraic g ↔ ∃ n, DifferentiallyAlgebraicOfOrder g n :=
  differentiallyAlgebraic_iff_exists_order

/-- **Theorem 3.1, clause 3, order form.**  Hypertranscendence is the failure of every finite
order bound. -/
theorem hypertranscendental_iff_forall_not_order (g : ℂ → ℂ) :
    Hypertranscendental g ↔ ∀ n : ℕ, ¬ DifferentiallyAlgebraicOfOrder g n := by
  constructor
  · intro h n hn
    exact h ⟨n, hn⟩
  · rintro h ⟨n, hn⟩
    exact h n hn

/-- **Equation (7).**  For an entire germ, hypertranscendence is exactly maximal algebraic
intervention growth: for every `N` the jets `f, Df, …, D^N f` of the meromorphic realization are
algebraically independent over `ℂ(z)`, i.e. `h_f(N) = N + 1`. -/
theorem hypertranscendental_iff_algebraicIndependent_jets {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ)) :
    Hypertranscendental g ↔ ∀ n : ℕ,
      (letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
          isPreconnected_univ Set.univ_nonempty
       letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
         (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
           Set.infinite_univ).toAlgebra
       letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
         Set.univ_nonempty
       AlgebraicIndependent (RatFunc ℂ)
         (fun j : Fin (n + 1) => differentialJet (j : ℕ) (analyticMeroElement g hg))) := by
  rw [hypertranscendental_iff_forall_not_order]
  exact forall_congr' fun n => (algebraicIndependent_jets_iff hg).symm

end AlgebraicMemory

/-! ## §4.1, remaining clauses, and §4.3 -/

section WitnessProfiles

open GaloisForLFunctions

/-- **Equation (10), second component.**  Every jet of `exp (z²)` is a polynomial multiple of
`exp (z²)`, so its base-aware linear memory is one. -/
theorem linearMemoryAtMost_expSq : LinearMemoryAtMost expSq (Set.univ : Set ℂ) 1 := by
  intro N
  refine ⟨fun _ => gaussianJetPoly N, 1, one_ne_zero, fun z _ => ?_⟩
  rw [Polynomial.eval_one, one_mul, Finset.sum_range_one, iteratedDeriv_zero,
    iteratedDeriv_expSq N]

/-- `exp (z²)` is `D`-finite of order one. -/
theorem dFiniteOn_expSq : DFiniteOn expSq (Set.univ : Set ℂ) :=
  dFiniteOn_of_linearMemoryAtMost linearMemoryAtMost_expSq

/-- **Equation (12).**  The shifted Gamma germ is hypertranscendental: no algebraic differential
equation of any order holds, so its algebraic intervention profile is maximal. -/
theorem hypertranscendental_gammaShift :
    Hypertranscendental fun z : ℂ => Complex.Gamma (z + 1) := by
  have h := hypertranscendental_gamma_affine (c := (1 : ℂ)) one_ne_zero 1
  simpa using h

theorem not_differentiallyAlgebraicOfOrder_gammaShift (n : ℕ) :
    ¬ DifferentiallyAlgebraicOfOrder (fun z : ℂ => Complex.Gamma (z + 1)) n :=
  (hypertranscendental_iff_forall_not_order _).mp hypertranscendental_gammaShift n

end WitnessProfiles

/-! ## §4.2 — finite algebraic memory without finite linear memory: `tan` -/

section TangentWitness

open Filter Topology

/-- The regular set of the tangent germ. -/
def tanRegular : Set ℂ := {z : ℂ | Complex.cos z ≠ 0}

theorem isOpen_tanRegular : IsOpen tanRegular :=
  isOpen_compl_iff.mpr (isClosed_eq Complex.continuous_cos continuous_const)

/-- The polynomial expressing the `i`-th jet of `tan` as a polynomial in `tan`. -/
noncomputable def tanJetPoly : ℕ → Polynomial ℂ
  | 0 => Polynomial.X
  | i + 1 => (1 + Polynomial.X ^ (2 : ℕ)) * Polynomial.derivative (tanJetPoly i)

theorem tan_sq_add_one {z : ℂ} (hz : Complex.cos z ≠ 0) :
    1 + Complex.tan z ^ (2 : ℕ) = 1 / Complex.cos z ^ (2 : ℕ) := by
  rw [Complex.tan_eq_sin_div_cos, div_pow]
  field_simp
  linear_combination Complex.sin_sq_add_cos_sq z

/-- **Equation (11), iterated.**  Every jet of `tan` is a polynomial in `tan`. -/
theorem eventually_iteratedDeriv_tan (i : ℕ) {a : ℂ} (ha : a ∈ tanRegular) :
    ∀ᶠ z in 𝓝 a, iteratedDeriv i Complex.tan z = (tanJetPoly i).eval (Complex.tan z) := by
  induction i generalizing a with
  | zero =>
    filter_upwards with z
    rw [iteratedDeriv_zero, tanJetPoly]
    simp
  | succ i ih =>
    have hnhds : ∀ᶠ z in 𝓝 a, z ∈ tanRegular := isOpen_tanRegular.mem_nhds ha
    filter_upwards [hnhds] with z hz
    have hev : iteratedDeriv i Complex.tan
        =ᶠ[𝓝 z] fun w => (tanJetPoly i).eval (Complex.tan w) := ih hz
    have hdtan : HasDerivAt Complex.tan (1 / Complex.cos z ^ (2 : ℕ)) z :=
      Complex.hasDerivAt_tan hz
    have hcomp : HasDerivAt (fun w => (tanJetPoly i).eval (Complex.tan w))
        ((Polynomial.derivative (tanJetPoly i)).eval (Complex.tan z)
          * (1 / Complex.cos z ^ (2 : ℕ))) z :=
      ((tanJetPoly i).hasDerivAt (Complex.tan z)).comp z hdtan
    rw [iteratedDeriv_succ, hev.deriv_eq, hcomp.deriv, tanJetPoly]
    rw [← tan_sq_add_one hz]
    simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_pow, Polynomial.eval_X]
    ring

theorem iteratedDeriv_tan {z : ℂ} (hz : z ∈ tanRegular) (i : ℕ) :
    iteratedDeriv i Complex.tan z = (tanJetPoly i).eval (Complex.tan z) :=
  (eventually_iteratedDeriv_tan i hz).self_of_nhds

theorem natDegree_tanJetPoly (i : ℕ) : (tanJetPoly i).natDegree = i + 1 := by
  induction i with
  | zero => simp [tanJetPoly]
  | succ i ih =>
    have hderiv : (Polynomial.derivative (tanJetPoly i)).natDegree = i := by
      rw [Polynomial.natDegree_derivative, ih]
      omega
    have hquad : ((1 : Polynomial ℂ) + Polynomial.X ^ (2 : ℕ)).natDegree = 2 := by
      compute_degree!
    have hne : Polynomial.derivative (tanJetPoly i) ≠ 0 := by
      rw [Polynomial.derivative_ne_zero, ih]
      omega
    have hquadne : (1 : Polynomial ℂ) + Polynomial.X ^ (2 : ℕ) ≠ 0 := by
      intro h0
      rw [h0] at hquad
      simp at hquad
    rw [tanJetPoly, Polynomial.natDegree_mul hquadne hne, hquad, hderiv]
    omega

/-- The quotient of a polynomial by the top power tends to the top coefficient along any filter
where the argument leaves every bounded set. -/
theorem tendsto_eval_div_pow {α : Type*} {l : Filter α} {t : α → ℂ} (P : Polynomial ℂ) {m : ℕ}
    (hdeg : P.natDegree ≤ m) (ht : Tendsto (fun a => ‖t a‖) l atTop) :
    Tendsto (fun a => P.eval (t a) / (t a) ^ m) l (𝓝 (P.coeff m)) := by
  have hinv : Tendsto (fun a => (t a)⁻¹) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [norm_inv]
    exact ht.inv_tendsto_atTop
  have hne : ∀ᶠ a in l, t a ≠ 0 := by
    filter_upwards [ht.eventually_gt_atTop 0] with a ha
    exact norm_pos_iff.mp ha
  have hform : ∀ᶠ a in l, P.eval (t a) / (t a) ^ m
      = ∑ j ∈ Finset.range (m + 1), P.coeff j * ((t a)⁻¹) ^ (m - j) := by
    filter_upwards [hne] with a ha
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjm : j ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    have hsplit : t a ^ m = t a ^ j * t a ^ (m - j) := by
      rw [← pow_add]
      congr 1
      omega
    rw [inv_pow, mul_div_assoc]
    congr 1
    rw [hsplit]
    field_simp
  refine Tendsto.congr' (hform.mono fun a ha => ha.symm) ?_
  have hlim : Tendsto (fun a => ∑ j ∈ Finset.range (m + 1), P.coeff j * ((t a)⁻¹) ^ (m - j)) l
      (𝓝 (∑ j ∈ Finset.range (m + 1), P.coeff j * (if j = m then 1 else 0))) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hjm : j ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    rcases eq_or_lt_of_le hjm with h | h
    · subst h
      simpa using tendsto_const_nhds
    · have hpow : Tendsto (fun a => ((t a)⁻¹) ^ (m - j)) l (𝓝 0) := by
        have : (0 : ℂ) = 0 ^ (m - j) := by
          rw [zero_pow (by omega)]
        rw [this]
        exact hinv.pow _
      have hjne : j ≠ m := by omega
      simpa [hjne] using tendsto_const_nhds.mul hpow
  have hval : ∑ j ∈ Finset.range (m + 1), P.coeff j * (if j = m then 1 else 0) = P.coeff m := by
    rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hm
      exact absurd (Finset.mem_range.mpr (by omega)) hm
  rwa [hval] at hlim

theorem tanJetPoly_ne_zero (i : ℕ) : tanJetPoly i ≠ 0 := by
  intro h0
  have := natDegree_tanJetPoly i
  rw [h0] at this
  simp at this

theorem coeff_tanJetPoly_of_lt {i n : ℕ} (h : i < n) : (tanJetPoly i).coeff (n + 1) = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
  rw [natDegree_tanJetPoly]
  omega

theorem coeff_tanJetPoly_top_ne_zero (n : ℕ) : (tanJetPoly n).coeff (n + 1) ≠ 0 := by
  have hd := natDegree_tanJetPoly n
  have : (tanJetPoly n).coeff (n + 1) = (tanJetPoly n).leadingCoeff := by
    rw [Polynomial.leadingCoeff, hd]
  rw [this]
  exact Polynomial.leadingCoeff_ne_zero.mpr (tanJetPoly_ne_zero n)

/-- **`tan` has no finite base-aware linear memory.**  A linear differential equation with
polynomial coefficients would have to degenerate at a pole where its leading coefficient is
regular: dividing by the top power of `tan` and letting `z` approach the pole forces that
coefficient to vanish. -/
theorem not_dFiniteOn_tan : ¬ DFiniteOn Complex.tan tanRegular := by
  rintro ⟨n, c, hcn, hrel⟩
  -- a pole at which the leading coefficient is regular
  have hpole : ∃ k : ℕ, (c n).eval ((2 * (k : ℤ) + 1) * (Real.pi : ℂ) / 2) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hinj : Function.Injective
        fun k : ℕ => (2 * (k : ℤ) + 1) * (Real.pi : ℂ) / 2 := by
      intro x y hxy
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hxy
      have hz : (2 : ℤ) * (x : ℤ) + 1 = 2 * (y : ℤ) + 1 := by exact_mod_cast hxy
      omega
    exact hcn (Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_of_injective_forall_mem hinj fun k => hall k))
  obtain ⟨k, hk⟩ := hpole
  set a : ℂ := (2 * (k : ℤ) + 1) * (Real.pi : ℂ) / 2 with ha
  have hcos : Complex.cos a = 0 := Complex.cos_eq_zero_iff.mpr ⟨k, by rw [ha]⟩
  have hnorm : Filter.Tendsto (fun z => ‖Complex.tan z‖) (nhdsWithin a {a}ᶜ) Filter.atTop :=
    Complex.tendsto_norm_tan_of_cos_eq_zero hcos
  have hreg : ∀ᶠ z in nhdsWithin a {a}ᶜ, z ∈ tanRegular := by
    filter_upwards [hnorm.eventually_gt_atTop 0] with z hz
    intro hcz
    rw [Complex.tan_eq_sin_div_cos, hcz, div_zero, norm_zero] at hz
    exact lt_irrefl 0 hz
  -- the normalized relation vanishes identically near the pole
  have hzero : ∀ᶠ z in nhdsWithin a {a}ᶜ, ∑ i ∈ Finset.range (n + 1),
      (c i).eval z * ((tanJetPoly i).eval (Complex.tan z) / Complex.tan z ^ (n + 1)) = 0 := by
    filter_upwards [hreg] with z hz
    have hsum := hrel z hz
    calc ∑ i ∈ Finset.range (n + 1),
          (c i).eval z * ((tanJetPoly i).eval (Complex.tan z) / Complex.tan z ^ (n + 1))
        = (∑ i ∈ Finset.range (n + 1), (c i).eval z * iteratedDeriv i Complex.tan z)
            / Complex.tan z ^ (n + 1) := by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [iteratedDeriv_tan hz i, mul_div_assoc]
      _ = 0 := by rw [hsum, zero_div]
  -- but its limit at the pole is the leading coefficient
  have hlim : Filter.Tendsto (fun z => ∑ i ∈ Finset.range (n + 1),
      (c i).eval z * ((tanJetPoly i).eval (Complex.tan z) / Complex.tan z ^ (n + 1)))
      (nhdsWithin a {a}ᶜ)
      (nhds (∑ i ∈ Finset.range (n + 1), (c i).eval a * (tanJetPoly i).coeff (n + 1))) := by
    refine tendsto_finsetSum _ fun i hi => ?_
    have hin : i < n + 1 := Finset.mem_range.mp hi
    have hc : Filter.Tendsto (fun z => (c i).eval z) (nhdsWithin a {a}ᶜ) (nhds ((c i).eval a)) :=
      ((c i).continuous_aeval.tendsto a).mono_left nhdsWithin_le_nhds
    have hq := tendsto_eval_div_pow (l := nhdsWithin a ({a}ᶜ : Set ℂ))
      (t := Complex.tan) (tanJetPoly i) (m := n + 1)
      (by rw [natDegree_tanJetPoly]; omega) hnorm
    exact hc.mul hq
  have hval : ∑ i ∈ Finset.range (n + 1), (c i).eval a * (tanJetPoly i).coeff (n + 1)
      = (c n).eval a * (tanJetPoly n).coeff (n + 1) := by
    rw [Finset.sum_eq_single n]
    · intro i hi hin
      have hilt : i < n := by
        have := Finset.mem_range.mp hi
        omega
      rw [coeff_tanJetPoly_of_lt hilt, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  rw [hval] at hlim
  have hzerolim : Filter.Tendsto (fun z => ∑ i ∈ Finset.range (n + 1),
      (c i).eval z * ((tanJetPoly i).eval (Complex.tan z) / Complex.tan z ^ (n + 1)))
      (nhdsWithin a {a}ᶜ) (nhds 0) :=
    Filter.Tendsto.congr' (hzero.mono fun z hz => hz.symm) tendsto_const_nhds
  have := tendsto_nhds_unique hlim hzerolim
  exact (mul_ne_zero hk (coeff_tanJetPoly_top_ne_zero n)) this

/-- **Equation (11).**  `tan` satisfies the order-one algebraic differential equation
`f' = 1 + f²` on its regular set. -/
theorem differentiallyAlgebraicOn_tan : DifferentiallyAlgebraicOn Complex.tan tanRegular := by
  refine ⟨1, MvPolynomial.X 2 - 1 - MvPolynomial.X 1 ^ (2 : ℕ), ?_, ?_⟩
  · intro h0
    have hev := congrArg
      (MvPolynomial.eval (fun i : Fin 3 => if i = 2 then (2 : ℂ) else 0)) h0
    simp at hev
    exact absurd hev (by norm_num)
  · intro z hz
    have hd : iteratedDeriv 1 Complex.tan z = 1 + Complex.tan z ^ (2 : ℕ) := by
      rw [iteratedDeriv_one, (Complex.hasDerivAt_tan hz).deriv, tan_sq_add_one hz]
    have h0 : iteratedDeriv 0 Complex.tan z = Complex.tan z := by rw [iteratedDeriv_zero]
    have hc0 : ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) Complex.tan z : Fin 3 → ℂ)) 1
        = iteratedDeriv 0 Complex.tan z := by
      show ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) Complex.tan z : Fin 3 → ℂ))
        (Fin.succ 0) = _
      rw [Fin.cons_succ]
      norm_num
    have hc1 : ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) Complex.tan z : Fin 3 → ℂ)) 2
        = iteratedDeriv 1 Complex.tan z := by
      show ((Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) Complex.tan z : Fin 3 → ℂ))
        (Fin.succ 1) = _
      rw [Fin.cons_succ]
      norm_num
    simp only [map_sub, map_pow, map_one, MvPolynomial.eval_X]
    rw [hc0, hc1, hd, h0]
    ring

/-! ### Transcendence of the two witnesses over `ℂ(z)` -/

/-- Algebraicity over `ℂ(z)` on a set, cleared of denominators. -/
def AlgebraicOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ (d : ℕ) (c : ℕ → Polynomial ℂ), c d ≠ 0 ∧
    ∀ z ∈ U, ∑ j ∈ Finset.range (d + 1), (c j).eval z * f z ^ j = 0

/-- A complex polynomial vanishing in the limit along the real axis is zero. -/
theorem eq_zero_of_tendsto_zero_atTop_real {P : Polynomial ℂ}
    (h : Filter.Tendsto (fun x : ℝ => P.eval ((x : ℝ) : ℂ)) Filter.atTop (nhds 0)) : P = 0 := by
  by_contra hP
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hnorm : Filter.Tendsto (fun x : ℝ => ‖((x : ℝ) : ℂ)‖) Filter.atTop Filter.atTop := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using Filter.tendsto_abs_atTop_atTop
  have hq := tendsto_eval_div_pow (l := Filter.atTop) (t := fun x : ℝ => ((x : ℝ) : ℂ)) P
    (m := P.natDegree) le_rfl hnorm
  have hzero : Filter.Tendsto (fun x : ℝ => P.eval ((x : ℝ) : ℂ) / ((x : ℝ) : ℂ) ^ P.natDegree)
      Filter.atTop (nhds 0) := by
    have hnormzero : Filter.Tendsto (fun x : ℝ => ‖P.eval ((x : ℝ) : ℂ)‖) Filter.atTop
        (nhds 0) := by
      simpa using h.norm
    refine squeeze_zero_norm' ?_ hnormzero
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx1 : (1 : ℝ) ≤ ‖((x : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_trans hx (le_abs_self x)
    have hxpos : (0 : ℝ) < ‖((x : ℝ) : ℂ)‖ ^ P.natDegree := by
      refine pow_pos ?_ _
      linarith
    rw [norm_div, norm_pow, div_le_iff₀ hxpos]
    calc ‖P.eval ((x : ℝ) : ℂ)‖ = ‖P.eval ((x : ℝ) : ℂ)‖ * 1 := (mul_one _).symm
      _ ≤ ‖P.eval ((x : ℝ) : ℂ)‖ * ‖((x : ℝ) : ℂ)‖ ^ P.natDegree :=
          mul_le_mul_of_nonneg_left (one_le_pow₀ hx1) (norm_nonneg _)
  exact hlead (tendsto_nhds_unique hq hzero)

/-- The dominating real polynomial of a complex polynomial. -/
noncomputable def normPoly (P : Polynomial ℂ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), Polynomial.C ‖P.coeff k‖ * Polynomial.X ^ k

theorem norm_eval_le_normPoly (P : Polynomial ℂ) {x : ℝ} (hx : 0 ≤ x) :
    ‖P.eval ((x : ℝ) : ℂ)‖ ≤ (normPoly P).eval x := by
  rw [Polynomial.eval_eq_sum_range' (n := P.natDegree + 1) (by omega), normPoly,
    Polynomial.eval_finsetSum]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]

/-- **`tan` is transcendental over `ℂ(z)`.**  A polynomial relation would survive division by the
top power of `tan` at a pole where its leading coefficient is regular. -/
theorem not_algebraicOn_tan : ¬ AlgebraicOn Complex.tan tanRegular := by
  rintro ⟨d, c, hcd, hrel⟩
  have hpole : ∃ k : ℕ, (c d).eval ((2 * (k : ℤ) + 1) * (Real.pi : ℂ) / 2) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have hinj : Function.Injective
        fun k : ℕ => (2 * (k : ℤ) + 1) * (Real.pi : ℂ) / 2 := by
      intro x y hxy
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hxy
      have hz : (2 : ℤ) * (x : ℤ) + 1 = 2 * (y : ℤ) + 1 := by exact_mod_cast hxy
      omega
    exact hcd (Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_of_injective_forall_mem hinj fun k => hall k))
  obtain ⟨k, hk⟩ := hpole
  set a : ℂ := (2 * (k : ℤ) + 1) * (Real.pi : ℂ) / 2 with ha
  have hcos : Complex.cos a = 0 := Complex.cos_eq_zero_iff.mpr ⟨k, by rw [ha]⟩
  have hnorm : Filter.Tendsto (fun z => ‖Complex.tan z‖) (nhdsWithin a {a}ᶜ) Filter.atTop :=
    Complex.tendsto_norm_tan_of_cos_eq_zero hcos
  have hreg : ∀ᶠ z in nhdsWithin a {a}ᶜ, z ∈ tanRegular := by
    filter_upwards [hnorm.eventually_gt_atTop 0] with z hz
    intro hcz
    rw [Complex.tan_eq_sin_div_cos, hcz, div_zero, norm_zero] at hz
    exact lt_irrefl 0 hz
  have hzero : ∀ᶠ z in nhdsWithin a {a}ᶜ, ∑ j ∈ Finset.range (d + 1),
      (c j).eval z * (Complex.tan z ^ j / Complex.tan z ^ d) = 0 := by
    filter_upwards [hreg] with z hz
    calc ∑ j ∈ Finset.range (d + 1), (c j).eval z * (Complex.tan z ^ j / Complex.tan z ^ d)
        = (∑ j ∈ Finset.range (d + 1), (c j).eval z * Complex.tan z ^ j) / Complex.tan z ^ d := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun j _ => by rw [mul_div_assoc]
      _ = 0 := by rw [hrel z hz, zero_div]
  have hlim : Filter.Tendsto (fun z => ∑ j ∈ Finset.range (d + 1),
      (c j).eval z * (Complex.tan z ^ j / Complex.tan z ^ d)) (nhdsWithin a {a}ᶜ)
      (nhds (∑ j ∈ Finset.range (d + 1),
        (c j).eval a * (Polynomial.X ^ j : Polynomial ℂ).coeff d)) := by
    refine tendsto_finsetSum _ fun j hj => ?_
    have hjd : j < d + 1 := Finset.mem_range.mp hj
    have hc : Filter.Tendsto (fun z => (c j).eval z) (nhdsWithin a {a}ᶜ) (nhds ((c j).eval a)) :=
      ((c j).continuous_aeval.tendsto a).mono_left nhdsWithin_le_nhds
    have hq := tendsto_eval_div_pow (l := nhdsWithin a ({a}ᶜ : Set ℂ))
      (t := Complex.tan) (Polynomial.X ^ j : Polynomial ℂ) (m := d)
      (by rw [Polynomial.natDegree_X_pow]; omega) hnorm
    simpa using hc.mul hq
  have hval : ∑ j ∈ Finset.range (d + 1),
      (c j).eval a * (Polynomial.X ^ j : Polynomial ℂ).coeff d = (c d).eval a := by
    rw [Finset.sum_eq_single d]
    · rw [Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro j _ hj
      rw [Polynomial.coeff_X_pow, if_neg (fun h => hj h.symm), mul_zero]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  rw [hval] at hlim
  exact hk (tendsto_nhds_unique hlim
    (Filter.Tendsto.congr' (hzero.mono fun z hz => hz.symm) tendsto_const_nhds))

/-- **`exp (z²)` is transcendental over `ℂ(z)`.**  Read on the real axis and divided by the top
exponential, a polynomial relation forces its leading coefficient to decay like `e^{-x}`. -/
theorem not_algebraicOn_expSq : ¬ AlgebraicOn expSq (Set.univ : Set ℂ) := by
  rintro ⟨d, c, hcd, hrel⟩
  have hexp : ∀ x : ℝ, expSq ((x : ℝ) : ℂ) = ((Real.exp (x ^ (2 : ℕ)) : ℝ) : ℂ) := by
    intro x
    rw [expSq, ← Complex.ofReal_pow, ← Complex.ofReal_exp]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0
    refine hcd (Polynomial.funext fun z => ?_)
    have h := hrel z (Set.mem_univ z)
    simpa using h
  · set S : Polynomial ℝ := ∑ j ∈ Finset.range d, normPoly (c j) with hS
    have hbound : ∀ x : ℝ, 1 ≤ x →
        ‖(c d).eval ((x : ℝ) : ℂ)‖ ≤ S.eval x / Real.exp x := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := le_trans zero_le_one hx
      have hEpos : (0 : ℝ) < Real.exp (x ^ (2 : ℕ)) := Real.exp_pos _
      have hE1 : (1 : ℝ) ≤ Real.exp (x ^ (2 : ℕ)) := Real.one_le_exp (by positivity)
      have hzero := hrel ((x : ℝ) : ℂ) (Set.mem_univ _)
      rw [Finset.sum_range_succ, hexp x] at hzero
      have hlead : (c d).eval ((x : ℝ) : ℂ) * ((Real.exp (x ^ (2 : ℕ)) : ℝ) : ℂ) ^ d
          = -∑ j ∈ Finset.range d,
            (c j).eval ((x : ℝ) : ℂ) * ((Real.exp (x ^ (2 : ℕ)) : ℝ) : ℂ) ^ j := by
        linear_combination hzero
      have hnormlead : ‖(c d).eval ((x : ℝ) : ℂ)‖ * Real.exp (x ^ (2 : ℕ)) ^ d
          ≤ ∑ j ∈ Finset.range d, ‖(c j).eval ((x : ℝ) : ℂ)‖ * Real.exp (x ^ (2 : ℕ)) ^ j := by
        have h1 : ‖(c d).eval ((x : ℝ) : ℂ) * ((Real.exp (x ^ (2 : ℕ)) : ℝ) : ℂ) ^ d‖
            = ‖(c d).eval ((x : ℝ) : ℂ)‖ * Real.exp (x ^ (2 : ℕ)) ^ d := by
          rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hEpos]
        rw [← h1, hlead, norm_neg]
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hEpos]
      have hupper : ∑ j ∈ Finset.range d, ‖(c j).eval ((x : ℝ) : ℂ)‖ * Real.exp (x ^ (2 : ℕ)) ^ j
          ≤ S.eval x * Real.exp (x ^ (2 : ℕ)) ^ (d - 1) := by
        rw [hS, Polynomial.eval_finsetSum, Finset.sum_mul]
        refine Finset.sum_le_sum fun j hj => ?_
        have hjd : j < d := Finset.mem_range.mp hj
        have hpow : Real.exp (x ^ (2 : ℕ)) ^ j ≤ Real.exp (x ^ (2 : ℕ)) ^ (d - 1) :=
          pow_le_pow_right₀ hE1 (by omega)
        have hnn : (0 : ℝ) ≤ (normPoly (c j)).eval x :=
          le_trans (norm_nonneg _) (norm_eval_le_normPoly (c j) hx0)
        calc ‖(c j).eval ((x : ℝ) : ℂ)‖ * Real.exp (x ^ (2 : ℕ)) ^ j
            ≤ (normPoly (c j)).eval x * Real.exp (x ^ (2 : ℕ)) ^ j :=
              mul_le_mul_of_nonneg_right (norm_eval_le_normPoly (c j) hx0) (by positivity)
          _ ≤ (normPoly (c j)).eval x * Real.exp (x ^ (2 : ℕ)) ^ (d - 1) :=
              mul_le_mul_of_nonneg_left hpow hnn
      have hsplit : Real.exp (x ^ (2 : ℕ)) ^ d = Real.exp (x ^ (2 : ℕ)) ^ (d - 1) * Real.exp (x ^ (2 : ℕ)) := by
        rw [← pow_succ]
        congr 1
        omega
      have hpow1 : (0 : ℝ) < Real.exp (x ^ (2 : ℕ)) ^ (d - 1) := pow_pos hEpos _
      have hkey : ‖(c d).eval ((x : ℝ) : ℂ)‖ * Real.exp (x ^ (2 : ℕ)) ≤ S.eval x := by
        have h := le_trans hnormlead hupper
        rw [hsplit] at h
        nlinarith [h, hpow1, norm_nonneg ((c d).eval ((x : ℝ) : ℂ))]
      have hxle : Real.exp x ≤ Real.exp (x ^ (2 : ℕ)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      have hexpos : (0 : ℝ) < Real.exp x := Real.exp_pos _
      rw [le_div_iff₀ hexpos]
      nlinarith [hkey, norm_nonneg ((c d).eval ((x : ℝ) : ℂ)), hxle]
    have hlim : Filter.Tendsto (fun x : ℝ => (c d).eval ((x : ℝ) : ℂ)) Filter.atTop (nhds 0) := by
      refine squeeze_zero_norm' ?_ (S.tendsto_div_exp_atTop)
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      exact hbound x hx
    exact hcd (eq_zero_of_tendsto_zero_atTop_real hlim)

end TangentWitness

/-! ## §4 and §5 — strict phase separation and the memory fingerprint -/

section MemorySpectrum

open GaloisForLFunctions

/-- **Equation (8), first implication.**  Finite constant-response memory gives a linear
differential equation with polynomial coefficients near the origin. -/
theorem dFiniteOn_of_bddHankelRank {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (h : BddHankelRank (respSeq f)) :
    ∃ U : Set ℂ, IsOpen U ∧ (0 : ℂ) ∈ U ∧ DFiniteOn f U := by
  obtain ⟨p, hp, hode⟩ := (seqConstantRecurrence_respSeq_iff_germConstantODE hf).mp
    (seqConstantRecurrence_of_bddHankelRank h)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hode
  refine ⟨Metric.ball (0 : ℂ) ε, Metric.isOpen_ball, Metric.mem_ball_self hε, ?_⟩
  refine ⟨p.natDegree, fun i => Polynomial.C (p.coeff i), ?_, fun z hz => ?_⟩
  · simpa using Polynomial.leadingCoeff_ne_zero.mpr hp
  · have hz' := hball (by simpa [Complex.dist_eq] using Metric.mem_ball.mp hz)
    rw [← hz']
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_C]

/-- **The doctrine-relative memory spectrum.**  The three memory doctrines are strictly
separated by three explicit germs: `exp (z²)` has infinite constant-response memory but a single
linear state; `tan` has no finite base-aware linear memory but an order-one algebraic relation;
the shifted Gamma germ has no algebraic differential relation of any order. -/
theorem doctrine_memory_spectrum :
    (¬ BddHankelRank (respSeq expSq)
        ∧ LinearMemoryAtMost expSq (Set.univ : Set ℂ) 1
        ∧ DifferentiallyAlgebraicOfOrder expSq 1
        ∧ ¬ AlgebraicOn expSq (Set.univ : Set ℂ))
      ∧ (¬ DFiniteOn Complex.tan tanRegular
        ∧ DifferentiallyAlgebraicOn Complex.tan tanRegular
        ∧ ¬ AlgebraicOn Complex.tan tanRegular)
      ∧ (∀ n : ℕ, ¬ DifferentiallyAlgebraicOfOrder (fun z : ℂ => Complex.Gamma (z + 1)) n) :=
  ⟨⟨not_bddHankelRank_expSq, linearMemoryAtMost_expSq, differentiallyAlgebraicOfOrder_expSq,
      not_algebraicOn_expSq⟩,
    ⟨not_dFiniteOn_tan, differentiallyAlgebraicOn_tan, not_algebraicOn_tan⟩,
    not_differentiallyAlgebraicOfOrder_gammaShift⟩

end MemorySpectrum

end GaloisForLFunctions.HTGeometry
