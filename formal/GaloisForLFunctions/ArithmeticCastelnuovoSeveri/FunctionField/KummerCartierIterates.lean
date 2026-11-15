import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierNaturality
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierRegularity

/-!
# Iterated Cartier extraction

Repeated Cartier extraction remains additive and natural under field
homomorphisms. Its scalar law extracts a `p^e`th root after `e` steps,
and every iterate preserves the intrinsic regular differential space.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.HTGeometry
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Repeated Cartier extraction on the actual Kähler module. -/
def squareKummerCartierIterate : ℕ →
    (KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R) →+
      KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R))
  | 0 => AddMonoidHom.id _
  | e + 1 => (squareKummerCoordinateCartier p s c b R).comp
      (squareKummerCartierIterate e)

/-- The zero iterate fixes every differential. -/
theorem squareKummerCartierIterate_zero
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    squareKummerCartierIterate p s c b R 0 ω = ω := rfl

/-- One additional iterate applies Cartier to the preceding iterate. -/
theorem squareKummerCartierIterate_succ (e : ℕ)
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    squareKummerCartierIterate p s c b R (e + 1) ω =
      squareKummerCoordinateCartier p s c b R (squareKummerCartierIterate p s c b R e ω) := rfl

/-- Adding iteration counts composes the corresponding Cartier iterates. -/
theorem squareKummerCartierIterate_add (e f : ℕ)
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    squareKummerCartierIterate p s c b R (e + f) ω =
      squareKummerCartierIterate p s c b R e (squareKummerCartierIterate p s c b R f ω) := by
  induction e with
  | zero => rfl
  | succ e ih => rw [Nat.succ_add, squareKummerCartierIterate_succ, ih,
      squareKummerCartierIterate_succ]

/-- Repeating one Cartier block multiplies its iteration count. -/
theorem squareKummerCartierIterate_mul (e f : ℕ)
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    squareKummerCartierIterate p s c b R (e * f) ω =
      (squareKummerCartierIterate p s c b R e : _ → _)^[f] ω := by
  induction f generalizing ω with
  | zero => rfl
  | succ f ih => rw [Nat.mul_succ, squareKummerCartierIterate_add, ih,
      Function.iterate_succ_apply]

/-- The `e`th Cartier iterate extracts the scalar root of a `p^e`th power. -/
theorem squareKummerCartierIterate_frobenius_smul (e : ℕ)
    (a : SquareKummerField p s c b R)
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    squareKummerCartierIterate p s c b R e (a ^ (p ^ e) • ω) =
      a • squareKummerCartierIterate p s c b R e ω := by
  induction e generalizing a ω with
  | zero => rw [squareKummerCartierIterate_zero, squareKummerCartierIterate_zero, pow_zero, pow_one]
  | succ e ih =>
    have ha : a ^ (p ^ (e + 1)) = (a ^ p) ^ (p ^ e) := by
      rw [pow_succ, ← pow_mul, Nat.mul_comm (p ^ e) p]
    rw [squareKummerCartierIterate_succ, ha, ih,
      squareKummerCoordinateCartier_frobenius_smul, squareKummerCartierIterate_succ]

/-- Every Cartier iterate sends each constant-field scalar line into the corresponding image line. -/
theorem squareKummerCartierIterate_scalar_line (e : ℕ) (a : SquareConstantField p s)
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    ∃ a' : SquareConstantField p s,
      squareKummerCartierIterate p s c b R e (a • ω) =
        a' • squareKummerCartierIterate p s c b R e ω := by
  induction e generalizing a ω with
  | zero => exact ⟨a, rfl⟩
  | succ e ih =>
    obtain ⟨a', ha'⟩ := ih a ω
    obtain ⟨a'', ha''⟩ := Finite.surjective_of_injective
      (frobenius (SquareConstantField p s) p).injective a'
    change a'' ^ p = a' at ha''
    refine ⟨a'', ?_⟩
    rw [squareKummerCartierIterate_succ, ha', squareKummerCartierIterate_succ]
    have hscale : a' • squareKummerCartierIterate p s c b R e ω =
        (algebraMap (SquareConstantField p s) (SquareKummerField p s c b R) a'') ^ p •
          squareKummerCartierIterate p s c b R e ω := by
      rw [← map_pow, ha'', IsScalarTower.algebraMap_smul]
    rw [hscale, squareKummerCoordinateCartier_frobenius_smul, IsScalarTower.algebraMap_smul]

/-- Every Cartier iterate preserves the actual global regular differential space. -/
theorem squareKummerCartierIterate_global_regular (d r e : ℕ)
    (ω : KaehlerDifferential (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)))
    (hω : ω ∈ globalRegularDifferentials (SquareConstantField p s)
      (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r))) :
    squareKummerCartierIterate p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) e ω ∈
      globalRegularDifferentials (SquareConstantField p s)
        (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) := by
  induction e with
  | zero => exact hω
  | succ e ih =>
    exact squareKummerCoordinateCartier_global_regular p s c d r _ ih

/-- Iterated Cartier extraction commutes with every constant-field homomorphism of Kummer models. -/
theorem squareKummerCartierIterate_map
    (c' : (SquareConstantField p s)ˣ) (b' R' e : ℕ)
    (f : SquareKummerField p s c b R →ₐ[SquareConstantField p s]
      SquareKummerField p s c' b' R')
    (ω : KaehlerDifferential (SquareConstantField p s) (SquareKummerField p s c b R)) :
    algHomKaehlerMap f (squareKummerCartierIterate p s c b R e ω) =
      squareKummerCartierIterate p s c' b' R' e (algHomKaehlerMap f ω) := by
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [squareKummerCartierIterate_succ, squareKummerCoordinateCartier_map,
      ih, squareKummerCartierIterate_succ]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
