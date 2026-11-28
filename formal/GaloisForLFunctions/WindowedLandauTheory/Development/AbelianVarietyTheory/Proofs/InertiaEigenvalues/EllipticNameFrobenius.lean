import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticCuspidalNames

/-! Rotation by Frobenius preserves regularity and the elliptic name
of a cuspidal character. -/

noncomputable section

open GlobalTheory.Published

namespace GlobalTheory.EllipticCharacters

variable {g n : ℕ} [Fact g.Prime] {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem character_pow_add (θ : Kˣ →* ℂˣ) (i j : ℕ) :
    (θ ^ g ^ i) ^ g ^ j = θ ^ g ^ (i + j) := by
  apply MonoidHom.ext
  intro z
  simp only [MonoidHom.pow_apply, ← pow_mul, pow_add]

private theorem character_pow_add_mul (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    (θ : Kˣ →* ℂˣ) (i j : ℕ) : θ ^ g ^ (i + n * j) = θ ^ g ^ i := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, Nat.add_comm (i + n * j), ← character_pow_add,
      char_frob hn hd, ih]

theorem regular_frobeniusPower (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    {θ : Kˣ →* ℂˣ} (hθ : IsRegularChar g n θ) (j : ℕ) : IsRegularChar g n (θ ^ g ^ j) := by
  intro a b ha hb hab
  apply hθ a b ha hb
  have hrec (i : ℕ) : ((θ ^ g ^ j) ^ g ^ i) ^ g ^ (n * j - j) = θ ^ g ^ i := by
    rw [character_pow_add, character_pow_add]
    have hj : j ≤ n * j := Nat.le_mul_of_pos_left j hn
    rw [show j + (i + (n * j - j)) = i + n * j by omega]
    exact character_pow_add_mul hn hd θ i j
  rw [← hrec a, ← hrec b, hab]

theorem regular_comp_residueEquiv {K' : Type} [Field K'] (e : K ≃+* K')
    {θ' : K'ˣ →* ℂˣ} (hθ' : IsRegularChar g n θ') :
    IsRegularChar g n (θ'.comp (Units.map e.toRingHom.toMonoidHom)) := by
  intro a b ha hb hab
  apply hθ' a b ha hb
  apply MonoidHom.ext
  intro z
  let w := Units.map e.symm.toRingHom.toMonoidHom z
  have hw : Units.map e.toRingHom.toMonoidHom w = z := by
    apply Units.ext
    exact e.apply_symm_apply (z : K')
  have he := DFunLike.congr_fun hab w
  simpa only [MonoidHom.pow_apply, MonoidHom.comp_apply, hw] using he

@[to_additive]
private theorem prod_range_rotate {M : Type*} [CommMonoid M] (hn : 0 < n)
    (f : ℕ → M) (hf : Function.Periodic f n) (j : ℕ) :
    ∏ i ∈ Finset.range n, f (i + j) = ∏ i ∈ Finset.range n, f i := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← ih, Finset.prod_range_succ (fun i => f (i + (j + 1))),
      Finset.prod_range_succ' (fun i => f (i + j))]
    have he : f (m + (j + 1)) = f (0 + j) := by
      rw [zero_add, show m + (j + 1) = j + (m + 1) by omega, hf j]
    rw [he]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    omega

private theorem unit_frob_periodic (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    (z : Kˣ) : Function.Periodic (fun i : ℕ => z ^ g ^ i) n := by
  intro i
  change z ^ g ^ (i + n) = z ^ g ^ i
  rw [Nat.add_comm i n, pow_add, pow_mul, unit_frob hn hd]

theorem HasEllipticName.frobeniusPower (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    {θ : Kˣ →* ℂˣ} {χ : GlobalTheory.GLq.Gn g n → ℂ} (hχ : HasEllipticName θ χ) (j : ℕ) :
    HasEllipticName (θ ^ g ^ j) χ := by
  intro y hy z hz
  rw [hχ y hy z hz]
  congr 1
  have hper : Function.Periodic (fun i : ℕ => (θ (z ^ g ^ i) : ℂ)) n := by
    intro i
    exact congrArg (fun u : Kˣ => (θ u : ℂ)) (unit_frob_periodic hn hd z i)
  rw [← sum_range_rotate hn _ hper j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MonoidHom.pow_apply, ← map_pow, ← pow_mul, ← pow_add]

theorem orbitPolynomial_frobeniusPower (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    (θ : Kˣ →* ℂˣ) (z : Kˣ) (j : ℕ) :
    ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (((θ ^ g ^ j) (z ^ g ^ i) : ℂˣ) : ℂ)) =
      ∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) := by
  have hper : Function.Periodic (fun i : ℕ => Polynomial.X - Polynomial.C (θ (z ^ g ^ i) : ℂ)) n := by
    intro i
    exact congrArg (fun u : Kˣ => Polynomial.X - Polynomial.C (θ u : ℂ))
      (unit_frob_periodic hn hd z i)
  rw [← prod_range_rotate hn _ hper j]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MonoidHom.pow_apply, ← map_pow, ← pow_mul, ← pow_add]

end GlobalTheory.EllipticCharacters

#print axioms GlobalTheory.EllipticCharacters.HasEllipticName.frobeniusPower
#print axioms GlobalTheory.EllipticCharacters.orbitPolynomial_frobeniusPower
