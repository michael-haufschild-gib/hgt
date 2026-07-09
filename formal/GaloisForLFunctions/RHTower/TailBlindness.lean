/-
# Tail blindness: asymptotic tiling conditions cannot force RH-grade parity

The logarithmic derivative of the `V₄`-orbit quartic `orbitQuartic ρ₀` is a sum of four simple
poles, `∑ (s − aᵢ)⁻¹`, whose norm is bounded by `4 / (s.re − M)` with `M` the largest real part
among the four roots.  It therefore vanishes as `s.re → ∞`: the quartic is invisible to any
condition that reads only the asymptotic shape of the logarithmic derivative at the arithmetic end.

Encode such a condition as `DlogTail F f`: the logarithmic derivative of `f` matches that of a
fixed reference `F` in the limit `re → ∞`.  Multiplication by `orbitQuartic ρ₀` changes the
logarithmic derivative by `(orbitQuartic ρ₀)′ / orbitQuartic ρ₀`, which the tail cannot see, so the
tail predicate is *stable* under orbit-quartic surgery (`dlogTail_orbitQuartic_mul`), as is eventual
nonvanishing (`eventuallyNonvanishing_orbitQuartic_mul`).  Feeding this stability into the banked
charge machinery (`carriesChargeAt_of_orbitQuartic_stable`) yields the capstone
`not_forcesRHParity_of_dlogTail`: the class of FE- and Schwarz-symmetric carriers matching a fixed
asymptotic tail carries off-line charge at `2 + I`, hence — through `forcesRHParity_iff_categorical`
— can never force RH-grade parity.  Rigidity of the arithmetic origami's tail cannot come from the
asymptotic tiling shape; it must consume an exact identity on a half-plane.

The complementary obstruction is finite-tail unfoldability (`toyCompletion_offline_defect`): the
exact single-prime completion `archFactor · (1 − p^{−s})⁻¹` inherits the archimedean factor's zero
at `s = 1`, uncancelled off the critical line.  In the full weld that zero is cancelled only by the
pole of the complete Euler product, i.e. by the divergence of the prime harmonic series.  Foldability
of the weld is an irreducibly infinite-ensemble effect: with the tail-blindness theorem, layer-6
rigidity requires the exact infinite-prime identity, nothing weaker.
-/
import GaloisForLFunctions.RHTower.MultiplicativeSoftness
import GaloisForLFunctions.RHTower.SymmetricDivisorRealization
import GaloisForLFunctions.RHTower.ZetaCarrier

open Complex Filter Topology

namespace RHTower

/-! ### §1 The logarithmic-derivative bound for the orbit quartic -/

/-- **Partial-fraction bound on the quartic's logarithmic derivative.**  For `s` with real part
beyond every root's real part (`M := max ρ₀.re (1 − ρ₀.re)`, which dominates all four orbit
real parts), the logarithmic derivative `(orbitQuartic ρ₀)′ / orbitQuartic ρ₀` equals the sum of
the four simple-pole terms `(s − aᵢ)⁻¹`, so its norm is at most `4 / (s.re − M)`. -/
theorem norm_dlog_orbitQuartic_le {ρ₀ s : ℂ}
    (hM : max ρ₀.re (1 - ρ₀.re) < s.re) :
    ‖deriv (orbitQuartic ρ₀) s / orbitQuartic ρ₀ s‖
      ≤ 4 / (s.re - max ρ₀.re (1 - ρ₀.re)) := by
  set M := max ρ₀.re (1 - ρ₀.re) with hMdef
  have hpos : 0 < s.re - M := by linarith
  have hne : ∀ a : ℂ, a.re ≤ M → s - a ≠ 0 := by
    intro a ha h
    have hre : (s - a).re = 0 := by rw [h]; simp
    rw [Complex.sub_re] at hre; linarith
  have hbound : ∀ a : ℂ, a.re ≤ M → ‖(s - a)⁻¹‖ ≤ (s.re - M)⁻¹ := by
    intro a ha
    rw [norm_inv]
    have h1 : s.re - M ≤ ‖s - a‖ := by
      have h2 : (s - a).re ≤ ‖s - a‖ := Complex.re_le_norm _
      rw [Complex.sub_re] at h2; linarith
    have hle := one_div_le_one_div_of_le hpos h1
    simpa only [one_div] using hle
  have ha1 : ρ₀.re ≤ M := le_max_left _ _
  have ha2 : (1 - ρ₀).re ≤ M := by rw [Complex.sub_re, Complex.one_re]; exact le_max_right _ _
  have ha3 : (starRingEnd ℂ ρ₀).re ≤ M := by rw [Complex.conj_re]; exact le_max_left _ _
  have ha4 : (1 - starRingEnd ℂ ρ₀).re ≤ M := by
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; exact le_max_right _ _
  have hz1 : s - ρ₀ ≠ 0 := hne ρ₀ ha1
  have hz2 : s - (1 - ρ₀) ≠ 0 := hne (1 - ρ₀) ha2
  have hz3 : s - starRingEnd ℂ ρ₀ ≠ 0 := hne (starRingEnd ℂ ρ₀) ha3
  have hz4 : s - (1 - starRingEnd ℂ ρ₀) ≠ 0 := hne (1 - starRingEnd ℂ ρ₀) ha4
  have hpf : deriv (orbitQuartic ρ₀) s / orbitQuartic ρ₀ s
      = (s - ρ₀)⁻¹ + (s - (1 - ρ₀))⁻¹ + (s - starRingEnd ℂ ρ₀)⁻¹
        + (s - (1 - starRingEnd ℂ ρ₀))⁻¹ := by
    have hd := ((hasDerivAt_id s).sub_const ρ₀).mul
        ((((hasDerivAt_id s).sub_const (1 - ρ₀)).mul
          ((hasDerivAt_id s).sub_const (starRingEnd ℂ ρ₀))).mul
          ((hasDerivAt_id s).sub_const (1 - starRingEnd ℂ ρ₀)))
    have hderiv : deriv (orbitQuartic ρ₀) s = _ := hd.deriv
    rw [hderiv]
    simp only [Pi.mul_apply, id_eq]
    unfold orbitQuartic
    field_simp
    ring
  rw [hpf]
  calc ‖(s - ρ₀)⁻¹ + (s - (1 - ρ₀))⁻¹ + (s - starRingEnd ℂ ρ₀)⁻¹
        + (s - (1 - starRingEnd ℂ ρ₀))⁻¹‖
      ≤ ‖(s - ρ₀)⁻¹‖ + ‖(s - (1 - ρ₀))⁻¹‖ + ‖(s - starRingEnd ℂ ρ₀)⁻¹‖
        + ‖(s - (1 - starRingEnd ℂ ρ₀))⁻¹‖ :=
        (norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (s.re - M)⁻¹ + (s.re - M)⁻¹ + (s.re - M)⁻¹ + (s.re - M)⁻¹ :=
        add_le_add (add_le_add (add_le_add (hbound ρ₀ ha1) (hbound (1 - ρ₀) ha2))
          (hbound (starRingEnd ℂ ρ₀) ha3)) (hbound (1 - starRingEnd ℂ ρ₀) ha4)
    _ = 4 / (s.re - M) := by rw [div_eq_mul_inv]; ring

/-- The orbit quartic is nonvanishing beyond every root's real part: each of the four linear
factors `s − aᵢ` has positive real part there, hence is nonzero. -/
theorem orbitQuartic_ne_zero_of_re_large {ρ₀ s : ℂ}
    (hM : max ρ₀.re (1 - ρ₀.re) < s.re) : orbitQuartic ρ₀ s ≠ 0 := by
  have hne : ∀ a : ℂ, a.re ≤ max ρ₀.re (1 - ρ₀.re) → s - a ≠ 0 := by
    intro a ha h
    have hre : (s - a).re = 0 := by rw [h]; simp
    rw [Complex.sub_re] at hre; linarith
  unfold orbitQuartic
  refine mul_ne_zero (hne ρ₀ (le_max_left _ _)) (mul_ne_zero (mul_ne_zero ?_ ?_) ?_)
  · exact hne (1 - ρ₀) (by rw [Complex.sub_re, Complex.one_re]; exact le_max_right _ _)
  · exact hne (starRingEnd ℂ ρ₀) (by rw [Complex.conj_re]; exact le_max_left _ _)
  · exact hne (1 - starRingEnd ℂ ρ₀) (by
      rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; exact le_max_right _ _)

/-- **The quartic's logarithmic derivative vanishes toward the arithmetic end.**  For every `ε > 0`
there is a half-plane `re ≥ X` on which `‖(orbitQuartic ρ₀)′ / orbitQuartic ρ₀‖ < ε`: the quartic
is invisible to the asymptotic tiling. -/
theorem dlog_orbitQuartic_vanishes (ρ₀ : ℂ) :
    ∀ ε > 0, ∃ X : ℝ, ∀ s : ℂ, X ≤ s.re →
      ‖deriv (orbitQuartic ρ₀) s / orbitQuartic ρ₀ s‖ < ε := by
  intro ε hε
  refine ⟨max ρ₀.re (1 - ρ₀.re) + 4 / ε + 1, fun s hs => ?_⟩
  have hMlt : max ρ₀.re (1 - ρ₀.re) < s.re := by
    have : (0 : ℝ) ≤ 4 / ε := le_of_lt (div_pos (by norm_num) hε)
    linarith
  refine lt_of_le_of_lt (norm_dlog_orbitQuartic_le hMlt) ?_
  have hpos : 0 < s.re - max ρ₀.re (1 - ρ₀.re) := by linarith
  rw [div_lt_iff₀ hpos]
  have hlb : 4 / ε + 1 ≤ s.re - max ρ₀.re (1 - ρ₀.re) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlb hε.le
  have heq : ε * (4 / ε + 1) = 4 + ε := by field_simp
  linarith

/-! ### §2 The asymptotic-tail predicate and its quartic-blindness -/

/-- `DlogTail F f`: the logarithmic derivative of `f` matches that of the reference `F` in the limit
`re → ∞`.  An asymptotic-tiling condition on the arithmetic end. -/
def DlogTail (F f : ℂ → ℂ) : Prop :=
  ∀ ε > 0, ∃ X : ℝ, ∀ s : ℂ, X ≤ s.re → ‖deriv f s / f s - deriv F s / F s‖ < ε

/-- `EventuallyNonvanishing f`: `f` is nonzero on some right half-plane. -/
def EventuallyNonvanishing (f : ℂ → ℂ) : Prop :=
  ∃ X : ℝ, ∀ s : ℂ, X ≤ s.re → f s ≠ 0

/-- Eventual nonvanishing is preserved by orbit-quartic multiplication: the quartic is itself
nonvanishing far to the right. -/
theorem eventuallyNonvanishing_orbitQuartic_mul {ρ₀ : ℂ} {f : ℂ → ℂ}
    (hnv : EventuallyNonvanishing f) :
    EventuallyNonvanishing (fun s => orbitQuartic ρ₀ s * f s) := by
  obtain ⟨X, hX⟩ := hnv
  refine ⟨max X (max ρ₀.re (1 - ρ₀.re) + 1), fun s hs => ?_⟩
  have hsX : X ≤ s.re := le_trans (le_max_left _ _) hs
  have hsM : max ρ₀.re (1 - ρ₀.re) < s.re := by
    have := le_trans (le_max_right _ _) hs; linarith
  exact mul_ne_zero (orbitQuartic_ne_zero_of_re_large hsM) (hX s hsX)

/-- **Tail blindness of the quartic multiplication.**  If `f` matches the reference tail and is
eventually nonvanishing, so does `orbitQuartic ρ₀ · f`: the product rule contributes exactly the
quartic's logarithmic derivative, which vanishes toward `re → ∞`, so the tail is unchanged. -/
theorem dlogTail_orbitQuartic_mul {F f : ℂ → ℂ} {ρ₀ : ℂ}
    (hf : Differentiable ℂ f) (hnv : EventuallyNonvanishing f)
    (htail : DlogTail F f) :
    DlogTail F (fun s => orbitQuartic ρ₀ s * f s) := by
  intro ε hε
  obtain ⟨X₃, hX₃⟩ := hnv
  obtain ⟨X₁, hX₁⟩ := dlog_orbitQuartic_vanishes ρ₀ (ε / 2) (by positivity)
  obtain ⟨X₂, hX₂⟩ := htail (ε / 2) (by positivity)
  refine ⟨max (max X₁ X₂) (max X₃ (max ρ₀.re (1 - ρ₀.re) + 1)), fun s hs => ?_⟩
  have hs1 : X₁ ≤ s.re := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs2 : X₂ ≤ s.re := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs3 : X₃ ≤ s.re := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsM : max ρ₀.re (1 - ρ₀.re) < s.re := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs; linarith
  have hq_ne : orbitQuartic ρ₀ s ≠ 0 := orbitQuartic_ne_zero_of_re_large hsM
  have hf_ne : f s ≠ 0 := hX₃ s hs3
  have hderiv : deriv (fun s => orbitQuartic ρ₀ s * f s) s
      = deriv (orbitQuartic ρ₀) s * f s + orbitQuartic ρ₀ s * deriv f s :=
    deriv_mul (orbitQuartic_differentiable ρ₀).differentiableAt hf.differentiableAt
  have key : deriv (fun s => orbitQuartic ρ₀ s * f s) s / (orbitQuartic ρ₀ s * f s)
      = deriv (orbitQuartic ρ₀) s / orbitQuartic ρ₀ s + deriv f s / f s := by
    rw [hderiv]; field_simp
  show ‖deriv (fun s => orbitQuartic ρ₀ s * f s) s / (orbitQuartic ρ₀ s * f s)
      - deriv F s / F s‖ < ε
  have hrw : deriv (fun s => orbitQuartic ρ₀ s * f s) s / (orbitQuartic ρ₀ s * f s)
        - deriv F s / F s
      = deriv (orbitQuartic ρ₀) s / orbitQuartic ρ₀ s
        + (deriv f s / f s - deriv F s / F s) := by
    rw [key]; ring
  rw [hrw]
  have h1 : ‖deriv (orbitQuartic ρ₀) s / orbitQuartic ρ₀ s‖ < ε / 2 := hX₁ s hs1
  have h2 : ‖deriv f s / f s - deriv F s / F s‖ < ε / 2 := hX₂ s hs2
  have htri := norm_add_le (deriv (orbitQuartic ρ₀) s / orbitQuartic ρ₀ s)
    (deriv f s / f s - deriv F s / F s)
  linarith

/-! ### §3 The blindness capstone -/

/-- **Tail blindness cannot force RH-grade parity.**  The class of carriers that are FE- and
Schwarz-symmetric, eventually nonvanishing, and match a fixed asymptotic tail `F` is stable under
multiplication by `orbitQuartic (2 + I)`.  That stability plants nontrivial deck charge at the
off-line point `2 + I` (its real part is `2 ≠ 1/2`, its imaginary part `1 ≠ 0`), so the class
carries off-line charge and therefore cannot force RH-grade parity.  Rigidity of the arithmetic
tail cannot be read from the asymptotic tiling; it must consume an exact identity on a half-plane. -/
theorem not_forcesRHParity_of_dlogTail (F : ℂ → ℂ) {g : ℂ → ℂ}
    (hg : FESchwarz g) (hgnv : EventuallyNonvanishing g) (hgtail : DlogTail F g) :
    ¬ ForcesRHParity (fun f => FESchwarz f ∧ EventuallyNonvanishing f ∧ DlogTail F f) := by
  rw [forcesRHParity_iff_categorical]
  intro hcat
  apply hcat
  have h2re : (2 + I : ℂ).re = 2 := by simp
  have h2im : (2 + I : ℂ).im = 1 := by simp
  have hre : (2 + I : ℂ).re ≠ 1 / 2 := by rw [h2re]; norm_num
  have him : (2 + I : ℂ).im ≠ 0 := by rw [h2im]; norm_num
  refine ⟨2 + I, hre, ?_⟩
  have hgC : FESchwarz g ∧ EventuallyNonvanishing g ∧ DlogTail F g := ⟨hg, hgnv, hgtail⟩
  have hstab : FESchwarz (fun s => orbitQuartic (2 + I) s * g s) ∧
      EventuallyNonvanishing (fun s => orbitQuartic (2 + I) s * g s) ∧
      DlogTail F (fun s => orbitQuartic (2 + I) s * g s) :=
    ⟨(fESchwarz_orbitQuartic (2 + I)).mul hg,
     eventuallyNonvanishing_orbitQuartic_mul hgnv,
     dlogTail_orbitQuartic_mul hg.1 hgnv hgtail⟩
  have hga : AnalyticAt ℂ g (2 + I) := hg.1.analyticAt (2 + I)
  have hgford : analyticOrderAt g (2 + I) ≠ ⊤ := by
    intro htop
    have hev0 : g =ᶠ[nhds (2 + I)] (0 : ℂ → ℂ) := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz
      simpa using hz
    have hgan : AnalyticOnNhd ℂ g Set.univ := fun x _ => hg.1.analyticAt x
    obtain ⟨X, hX⟩ := hgnv
    have hzero : g ((X : ℂ)) = 0 :=
      hgan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (Set.mem_univ _) hev0 (Set.mem_univ _)
    exact hX (X : ℂ) (by simp) hzero
  exact carriesChargeAt_of_orbitQuartic_stable hre him hgC hstab hga hgford

/-! ### §4 Finite-tail unfoldability: the single-prime completion has an off-line defect -/

/-- The exact single-prime completion `archFactor · (1 − p^{−s})⁻¹`: the archimedean factor times
one Euler factor. -/
noncomputable def toyCompletion (p : ℕ) : ℂ → ℂ :=
  fun s => archFactor s * (1 - (p : ℂ) ^ (-s))⁻¹

/-- **The finite completion is unfoldable.**  For a prime base `p ≥ 2` the single-prime completion
`toyCompletion p` has a nonzero vanishing order at `s = 1`, which is off the critical line
(`(1 : ℂ).re = 1 ≠ 1/2`): the archimedean factor's zero at `s = 1` is uncancelled, since the single
Euler factor `(1 − p^{−s})⁻¹` is finite and nonzero there (`p^{−1} ≠ 1`).  In the full weld this
zero is cancelled only by the pole of the complete Euler product — the divergence of the prime
harmonic series — so foldability of the weld is an irreducibly infinite-ensemble effect. -/
theorem toyCompletion_offline_defect {p : ℕ} (hp : 2 ≤ p) :
    analyticOrderAt (toyCompletion p) 1 ≠ 0 ∧ ((1 : ℂ)).re ≠ 1 / 2 := by
  have hbase : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpne1 : (p : ℂ) ≠ 1 := by
    intro h; have : p = 1 := by exact_mod_cast h
    omega
  refine ⟨?_, by rw [Complex.one_re]; norm_num⟩
  rw [analyticOrderAt_ne_zero]
  refine ⟨?_, ?_⟩
  · have hG : Gammaℝ 1 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [Complex.one_re]; norm_num)
    have hpoly : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) 1 := by fun_prop
    have harch : AnalyticAt ℂ archFactor 1 := hpoly.mul (Gammaℝ_analyticAt hG)
    have hcpow_an : AnalyticAt ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) 1 := by
      have heq : (fun s : ℂ => (p : ℂ) ^ (-s))
          = fun s => Complex.exp (Complex.log (p : ℂ) * (-s)) := by
        funext s; rw [Complex.cpow_def_of_ne_zero hbase]
      rw [heq]
      have hd : Differentiable ℂ (fun s : ℂ => Complex.exp (Complex.log (p : ℂ) * (-s))) := by
        apply Differentiable.cexp; fun_prop
      exact hd.analyticAt 1
    have hne2 : (1 : ℂ) - (p : ℂ) ^ (-(1 : ℂ)) ≠ 0 := by
      rw [Complex.cpow_neg_one, sub_ne_zero]
      intro h
      rw [eq_comm, inv_eq_one] at h
      exact hpne1 h
    have hinv_an : AnalyticAt ℂ (fun s : ℂ => (1 - (p : ℂ) ^ (-s))⁻¹) 1 := by
      apply AnalyticAt.inv (analyticAt_const.sub hcpow_an)
      show (1 : ℂ) - (p : ℂ) ^ (-(1 : ℂ)) ≠ 0
      exact hne2
    exact harch.mul hinv_an
  · show toyCompletion p 1 = 0
    unfold toyCompletion archFactor
    ring

end RHTower
