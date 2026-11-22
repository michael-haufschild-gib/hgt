import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.IntegerModulus
import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.DataHost
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts

/-! Construct a host from a CM field and explicit choices of levels and Frobenius sets. -/

open NumberField WindowedLandauTheory.FrobeniusOrbits WindowedLandauTheory.TwoAdicCyclotomicDecomposition
open WindowedLandauTheory.HC WindowedLandauTheory.BasicNotions
open scoped Pointwise

noncomputable section

namespace HostParam.Seam

structure FieldRows {φ : Frame} (H : HostRaw φ) (b : ℕ) : Prop where
  psQ : H.PsQ
  sqq : ∃ s : H.E, s ^ 2 = -(H.q : H.E) ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ s = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * s
  QS_exact : H.Exact
  QS_le : H.QS ≤ φ.ord ^ 2
  o_pow : φ.o ^ 64 ≤ 2 ^ φ.e
  q_ne_three : H.q ≠ 3
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ b → jacobiSym (-(H.d : ℤ)) p = 1
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ H.QS → 4 * l ≤ b

structure Choices (φ : Frame) (H : HostRaw φ) where
  levelPrimes : Finset ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  g_level : ∀ i, g i ∈ levelPrimes
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_level : pde ∈ levelPrimes ∧ pde' ∈ levelPrimes
  pde_mod : pde % 15 = 1 ∧ pde' % 15 = 1
  pde_ne_g : ∀ i, pde ≠ g i ∧ pde' ≠ g i
  ccK : Ideal (𝓞 H.K)
  ccK_ne_bot : ccK ≠ ⊥
  ccK_primitive : ∀ m : ℕ, 1 < m → ¬ ccK ≤ Ideal.span {(m : 𝓞 H.K)}
  ccK_split : ∀ P : Ideal (𝓞 H.K), P.IsPrime → ccK ≤ P →
    (Ideal.absNorm P).Prime ∧ jacobiSym (-(H.d : ℤ)) (Ideal.absNorm P) = 1
  ccK_coprime : ∀ p ∈ insert 2 (insert 3 (insert 5 (insert H.q (insert H.d levelPrimes)))),
    Nat.Coprime (Ideal.absNorm ccK) p
  ccK_coprimeS : Nat.Coprime (Ideal.absNorm ccK) H.QS
  level_coprimeS : ∀ p ∈ levelPrimes, Nat.Coprime p H.QS
  TT : Finset φ.A
  T2 : Finset ℕ
  u0 : φ.A
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < φ.n0
  second_set_no_relation : NoRel T2 Lw
  CT2 : ℝ

private theorem exists_cm_type {φ : Frame} (H : HostAx φ) :
    ∃ ψ : H.E →+* ℂ, ψ ∈ H.toHostRaw.cmType := by
  have h := H.der.cmType.2.1
  have := φ.ord_pos
  exact Set.nonempty_of_ncard_ne_zero (by omega)

/-- Extend the underlying CM field using the chosen levels and Frobenius data. -/
noncomputable def host_of_fields (R : Ranks) (H : HostAx R.toFrame) {b : ℕ} (F : FieldRows H.toHostRaw b)
    (hq : 4 * R.t * R.r + 1 < H.q ∧ 4 * R.t * R.r + 1 < H.d) (c : Choices R.toFrame H.toHostRaw) :
    WindowedLandauTheory.BasicNotions.Host R :=
  let s := Classical.choose F.sqq
  let hs := Classical.choose_spec F.sqq
  let ψ := Classical.choose (exists_cm_type H)
  let hψ := Classical.choose_spec (exists_cm_type H)
  let 𝔟 := Classical.choose H.der.principal
  let hb := Classical.choose_spec H.der.principal
  { H, c with
    flPS := F.psQ, sqq := s, sqq_sq := hs.1, gal_sqq := hs.2
    QS_exact := F.QS_exact, QS_le := F.QS_le, o_pow := F.o_pow, q_ne_three := F.q_ne_three
    qd_big := hq, splitBound := b, split_small := F.split_small, small_le := F.small_le
    φ₀ := ψ, φ₀_mem := hψ, 𝔟 := 𝔟, 𝔟_spec := ⟨hb.1, hb.2.1⟩, 𝔟_stable := hb.2.2 }

theorem nonempty_choices {φ : Frame} (H : HostRaw φ) : Nonempty (Choices φ H) := by
  classical
  obtain ⟨a, hla, ha⟩ := Nat.exists_infinite_primes (H.QS + 1)
  obtain ⟨b, hlb, hb⟩ := Nat.exists_infinite_primes (a + 1)
  obtain ⟨c, hc, hbc, hc1⟩ := Nat.exists_prime_gt_modEq_one (k := 15) b (by norm_num)
  obtain ⟨d, hd, hcd, hd1⟩ := Nat.exists_prime_gt_modEq_one (k := 15) c (by norm_num)
  have cop : ∀ p : ℕ, p.Prime → H.QS < p → Nat.Coprime p H.QS := fun p hp hlt =>
    (Nat.Prime.coprime_iff_not_dvd hp).2 (fun hdv => absurd (Nat.le_of_dvd H.QS_pos hdv) (by omega))
  refine ⟨{
      levelPrimes := {a, b, c, d}
      g := ![a, b]
      g_prime := fun i => by fin_cases i <;> simpa
      g_ne := by simp; omega
      g_level := fun i => by fin_cases i <;> simp
      pde := c
      pde' := d
      pde_prime := hc
      pde'_prime := hd
      pde_ne := by omega
      pde_level := by simp
      pde_mod := ⟨by simpa [Nat.ModEq] using hc1, by simpa [Nat.ModEq] using hd1⟩
      pde_ne_g := fun i => by fin_cases i <;> simp <;> omega
      ccK := ⊤
      ccK_ne_bot := top_ne_bot
      ccK_primitive := fun m hm => Ideal.span_natCast_not_top_le _ m hm
      ccK_split := fun P hP hle => absurd (top_le_iff.mp hle) hP.ne_top
      ccK_coprime := by simp
      ccK_coprimeS := by simp
      level_coprimeS := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro p (rfl | rfl | rfl | rfl) <;> apply cop <;> first | assumption | omega
      TT := ∅
      T2 := ∅
      u0 := Classical.arbitrary _
      Lw := 2
      two_le_Lw := le_rfl
      second_set_range := by simp
      second_set_no_relation := by simp [NoRel]
      CT2 := 0 }⟩

end HostParam.Seam
