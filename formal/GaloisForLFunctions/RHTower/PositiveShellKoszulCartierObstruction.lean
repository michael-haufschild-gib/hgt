import GaloisForLFunctions.Bottcher.MeromorphicField
import GaloisForLFunctions.HTGeometry.CommonFactorKoszulHomology
import GaloisForLFunctions.RHTower.HighExponentShellSourcePole

/-!
# Positive-shell Koszul--Cartier obstruction

This module instantiates the two-generator common-factor Koszul calculation with the actual
high-positive-exponent shell sources on
`{s : ℂ | 1/2 < s.re} \ {1}`.  The carrier is the analytic-germ domain, the common regular factor
is the genuine Riemann zeta germ, and each shell multiplier is constructed as an actual unit from
its proved analyticity and zero-freeness.
-/

namespace RHTower

open Filter Set Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Punctured strict right half-plane carrying the positive shell frame. -/
def positiveShellDomain : Set ℂ := {s : ℂ | 1 / 2 < s.re} \ {1}

theorem isOpen_positiveShellDomain : IsOpen positiveShellDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton

theorem two_mem_positiveShellDomain : (2 : ℂ) ∈ positiveShellDomain := by
  constructor <;> norm_num

theorem positiveShellDomain_nonempty : positiveShellDomain.Nonempty :=
  ⟨2, two_mem_positiveShellDomain⟩

/-- The punctured strict right half-plane is preconnected. -/
theorem isPreconnected_positiveShellDomain : IsPreconnected positiveShellDomain := by
  set L : Set ℂ := {s | 1 / 2 < s.re ∧ s.re < 1} with hLdef
  set R : Set ℂ := {s | 1 < s.re} with hRdef
  set Up : Set ℂ := {s | 1 / 2 < s.re ∧ 0 < s.im} with hUpdef
  set Dn : Set ℂ := {s | 1 / 2 < s.re ∧ s.im < 0} with hDndef
  have pL : IsPreconnected L :=
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have pR : IsPreconnected R := (convex_halfSpace_re_gt 1).isPreconnected
  have pUp : IsPreconnected Up :=
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have pDn : IsPreconnected Dn :=
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have p1 : IsPreconnected (L ∪ Up) := by
    refine pL.union (((3 : ℝ) / 4 : ℂ) + Complex.I) ?_ ?_ pUp
    · exact ⟨by simp; norm_num, by norm_num⟩
    · exact ⟨by simp; norm_num, by simp⟩
  have p2 : IsPreconnected (L ∪ Up ∪ R) := by
    refine p1.union ((2 : ℂ) + Complex.I) ?_ ?_ pR
    · exact Or.inr ⟨by simp; norm_num, by simp⟩
    · change 1 < ((2 : ℂ) + Complex.I).re
      norm_num
  have p3 : IsPreconnected (L ∪ Up ∪ R ∪ Dn) := by
    refine p2.union (((3 : ℝ) / 4 : ℂ) - Complex.I) ?_ ?_ pDn
    · exact Or.inl (Or.inl ⟨by simp; norm_num, by norm_num⟩)
    · exact ⟨by simp; norm_num, by simp⟩
  have hset : positiveShellDomain = L ∪ Up ∪ R ∪ Dn := by
    apply Set.Subset.antisymm
    · intro s hs
      obtain ⟨hre, hne⟩ := hs
      rw [Set.mem_setOf_eq] at hre
      rw [Set.mem_singleton_iff] at hne
      rcases lt_trichotomy s.re 1 with h | h | h
      · exact Or.inl (Or.inl (Or.inl ⟨hre, h⟩))
      · have him : s.im ≠ 0 := by
          intro h0
          apply hne
          apply Complex.ext <;> simp [h, h0]
        rcases lt_or_gt_of_ne him with hlt | hgt
        · exact Or.inr ⟨hre, hlt⟩
        · exact Or.inl (Or.inl (Or.inr ⟨hre, hgt⟩))
      · exact Or.inl (Or.inr h)
    · refine Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) ?_) ?_
      · rintro s ⟨hre, hlt⟩
        exact ⟨hre, by rw [Set.mem_singleton_iff]; rintro rfl; simp at hlt⟩
      · rintro s ⟨hre, him⟩
        exact ⟨hre, by rw [Set.mem_singleton_iff]; rintro rfl; simp at him⟩
      · intro s hs
        rw [Set.mem_setOf_eq] at hs
        constructor
        · show (1 / 2 : ℝ) < s.re
          linarith
        · rw [Set.mem_singleton_iff]
          rintro rfl
          change 1 < (1 : ℂ).re at hs
          norm_num at hs
      · rintro s ⟨hre, him⟩
        exact ⟨hre, by rw [Set.mem_singleton_iff]; rintro rfl; simp at him⟩
  rw [hset]
  exact p3

/-- Analytic functions on the positive-shell domain, as faithful germs. -/
abbrev PositiveShellAnalyticRing := Bottcher.analyticSubring positiveShellDomain

noncomputable instance positiveShellAnalyticRingIsDomain : IsDomain PositiveShellAnalyticRing :=
  Bottcher.isDomain_analyticSubring positiveShellDomain isOpen_positiveShellDomain
    isPreconnected_positiveShellDomain positiveShellDomain_nonempty

theorem analyticOnNhd_riemannZeta_positiveShellDomain :
    AnalyticOnNhd ℂ riemannZeta positiveShellDomain :=
  analyticOn_riemannZeta.mono fun _ hs => hs.2

/-- Genuine zeta germ on the positive-shell domain. -/
def positiveShellZeta : PositiveShellAnalyticRing :=
  ⟨Germ.coeRingHom (𝓟 positiveShellDomain) riemannZeta,
    ⟨riemannZeta, analyticOnNhd_riemannZeta_positiveShellDomain, rfl⟩⟩

theorem positiveShellZeta_ne_zero : positiveShellZeta ≠ 0 := by
  intro h
  have hgerm := congrArg Subtype.val h
  rw [ZeroMemClass.coe_zero] at hgerm
  change (↑riemannZeta : Germ (𝓟 positiveShellDomain) ℂ) =
    (↑(0 : ℂ → ℂ) : Germ (𝓟 positiveShellDomain) ℂ) at hgerm
  rw [Germ.coe_eq] at hgerm
  have htwo : riemannZeta 2 = 0 := eventually_principal.mp hgerm 2 two_mem_positiveShellDomain
  exact (riemannZeta_ne_zero_of_one_lt_re (s := (2 : ℂ)) (by norm_num)) htwo

theorem positiveShellZeta_regular : IsKoszulRegular positiveShellZeta := by
  intro r hzr
  exact (mul_eq_zero.mp hzr).resolve_left positiveShellZeta_ne_zero

/-- Exponents for which shell multipliers are proved holomorphic and zero-free. -/
abbrev PositiveShellExponent := {m : ℕ // 12 ≤ m}

theorem analyticOnNhd_shellMultiplier_positiveShellDomain (m : PositiveShellExponent) :
    AnalyticOnNhd ℂ (shellMultiplier m.1) positiveShellDomain :=
  fun _ hs => analyticAt_shellMultiplier m.2 hs.1

/-- Genuine analytic shell multiplier germ. -/
def positiveShellMultiplier (m : PositiveShellExponent) : PositiveShellAnalyticRing :=
  ⟨Germ.coeRingHom (𝓟 positiveShellDomain) (shellMultiplier m.1),
    ⟨shellMultiplier m.1, analyticOnNhd_shellMultiplier_positiveShellDomain m, rfl⟩⟩

theorem analyticOnNhd_shellMultiplierInv_positiveShellDomain (m : PositiveShellExponent) :
    AnalyticOnNhd ℂ (fun s => (shellMultiplier m.1 s)⁻¹) positiveShellDomain :=
  fun _ hs => (analyticAt_shellMultiplier m.2 hs.1).inv (shellMultiplier_ne_zero m.2 hs.1)

/-- Analytic inverse of the shell multiplier germ. -/
def positiveShellMultiplierInv (m : PositiveShellExponent) : PositiveShellAnalyticRing :=
  ⟨Germ.coeRingHom (𝓟 positiveShellDomain) (fun s => (shellMultiplier m.1 s)⁻¹),
    ⟨fun s => (shellMultiplier m.1 s)⁻¹,
      analyticOnNhd_shellMultiplierInv_positiveShellDomain m, rfl⟩⟩

/-- Each high-positive-exponent shell multiplier is an actual unit of the analytic carrier. -/
def positiveShellMultiplierUnit (m : PositiveShellExponent) : PositiveShellAnalyticRingˣ where
  val := positiveShellMultiplier m
  inv := positiveShellMultiplierInv m
  val_inv := by
    apply Subtype.ext
    change (↑(shellMultiplier m.1) : Germ (𝓟 positiveShellDomain) ℂ) *
        (↑(fun s => (shellMultiplier m.1 s)⁻¹) : Germ (𝓟 positiveShellDomain) ℂ) = 1
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
    exact eventually_principal.mpr fun s hs => by
      simp [shellMultiplier_ne_zero m.2 hs.1]
  inv_val := by
    apply Subtype.ext
    change (↑(fun s => (shellMultiplier m.1 s)⁻¹) : Germ (𝓟 positiveShellDomain) ℂ) *
        (↑(shellMultiplier m.1) : Germ (𝓟 positiveShellDomain) ℂ) = 1
    rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
    exact eventually_principal.mpr fun s hs => by
      simp [shellMultiplier_ne_zero m.2 hs.1]

/-- Analytic germ of the actual shell source `S_m = ζ H_m`. -/
def positiveShellSource (m : PositiveShellExponent) : PositiveShellAnalyticRing :=
  positiveShellZeta * positiveShellMultiplierUnit m

theorem positiveShellSource_coe (m : PositiveShellExponent) :
    (positiveShellSource m : Germ (𝓟 positiveShellDomain) ℂ) =
      Germ.coeRingHom (𝓟 positiveShellDomain) (shellSource m.1) := by
  rw [positiveShellSource, MulMemClass.coe_mul]
  change (↑riemannZeta : Germ (𝓟 positiveShellDomain) ℂ) *
      (↑(shellMultiplier m.1) : Germ (𝓟 positiveShellDomain) ℂ) =
    ↑(shellSource m.1)
  rw [← Germ.coe_mul]
  rfl

/-- Actual degree-one shell-pair differential. -/
abbrev positiveShellKoszulD1 (m n : PositiveShellExponent) :=
  commonFactorKoszulD1 positiveShellZeta (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n)

/-- Actual degree-two shell-pair differential. -/
abbrev positiveShellKoszulD2 (m n : PositiveShellExponent) :=
  commonFactorKoszulD2 positiveShellZeta (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n)

abbrev positiveShellKoszulH0 (m n : PositiveShellExponent) :=
  commonFactorKoszulH0 positiveShellZeta (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n)

abbrev positiveShellKoszulH1 (m n : PositiveShellExponent) :=
  commonFactorKoszulH1 positiveShellZeta (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n)

abbrev positiveShellKoszulH2 (m n : PositiveShellExponent) :=
  commonFactorKoszulH2 positiveShellZeta (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n)

/-- Degree zero is the Riemann Cartier divisor ring. -/
def positiveShellKoszulH0Equiv (m n : PositiveShellExponent) :
    positiveShellKoszulH0 m n ≃ₗ[PositiveShellAnalyticRing]
      PositiveShellAnalyticRing ⧸
        (Ideal.span ({positiveShellZeta} : Set PositiveShellAnalyticRing) :
          Submodule PositiveShellAnalyticRing PositiveShellAnalyticRing) :=
  commonFactorKoszulH0Equiv positiveShellZeta (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n)

/-- Degree one is the same divisor ring, generated by the source syzygy `(H_n,-H_m)`. -/
def positiveShellKoszulH1Equiv (m n : PositiveShellExponent) :
    positiveShellKoszulH1 m n ≃ₗ[PositiveShellAnalyticRing]
      PositiveShellAnalyticRing ⧸
        (Ideal.span ({positiveShellZeta} : Set PositiveShellAnalyticRing) :
          Submodule PositiveShellAnalyticRing PositiveShellAnalyticRing) :=
  commonFactorKoszulH1Equiv (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n) positiveShellZeta_regular

/-- Degree two vanishes. -/
theorem positiveShellKoszulH2_eq_bot (m n : PositiveShellExponent) :
    positiveShellKoszulH2 m n = ⊥ :=
  commonFactorKoszulH2_eq_bot (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n) positiveShellZeta_regular

/-- Degree-one shell obstruction is exactly the principal zeta conormal line. -/
def positiveShellKoszulH1CotangentEquiv (m n : PositiveShellExponent) :
    positiveShellKoszulH1 m n ≃ₗ[PositiveShellAnalyticRing]
      (Ideal.span ({positiveShellZeta} : Set PositiveShellAnalyticRing)).Cotangent :=
  commonFactorKoszulH1CotangentEquiv (positiveShellMultiplierUnit m)
    (positiveShellMultiplierUnit n) positiveShellZeta_regular

/-- Source syzygy identity `H_n S_m - H_m S_n = 0` in the faithful analytic carrier. -/
theorem positiveShell_source_syzygy (m n : PositiveShellExponent) :
    positiveShellKoszulD1 m n
      ((positiveShellMultiplierUnit n : PositiveShellAnalyticRing),
        -(positiveShellMultiplierUnit m : PositiveShellAnalyticRing)) = 0 := by
  simp [commonFactorKoszulD1]
  ring

end

end RHTower
