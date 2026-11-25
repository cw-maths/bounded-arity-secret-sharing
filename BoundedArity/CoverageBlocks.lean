module

public import BoundedArity.LinearRank
public import Mathlib.Data.Fintype.BigOperators

/-!
# Private coordinates and shared padding blocks

A block consists of `n` free coordinates, observed in full by each member
of a specified holder set. A coalition sees the whole block exactly when
it meets that set. Private coordinates are the singleton-holder case.
-/

@[expose] public section

namespace BoundedArity

open scoped BigOperators

variable {E : Type*} [DecidableEq E]

/-- Every holder sees all coordinates in this independent block. -/
def heldSpace (K : Type*) [Field K] (H : Finset E) (n : ℕ) (i : E) :
    Submodule K (Fin n → K) :=
  if i ∈ H then ⊤ else ⊥

theorem jointSubspace_heldSpace (K : Type*) [Field K]
    (H : Finset E) (n : ℕ) (U : Finset E) :
    jointSubspace (heldSpace K H n) U =
      if (U ∩ H).Nonempty then ⊤ else ⊥ := by
  classical
  by_cases h : (U ∩ H).Nonempty
  · rw [ite_eq_left h]
    apply top_unique
    obtain ⟨p, hp⟩ := h
    obtain ⟨hpU, hpH⟩ := Finset.mem_inter.mp hp
    have htop : heldSpace K H n p = ⊤ := by simp [heldSpace, hpH]
    rw [← htop]
    exact le_jointSubspace (heldSpace K H n) U hpU
  · rw [ite_eq_right h]
    apply bot_unique
    unfold jointSubspace
    refine iSup_le (fun p => iSup_le (fun hpU => ?_))
    have hpH : p ∉ H := by
      intro hpH
      exact h ⟨p, Finset.mem_inter.mpr ⟨hpU, hpH⟩⟩
    simp [heldSpace, hpH]

theorem heldSpace_joint_finrank (K : Type*) [Field K]
    (H : Finset E) (n : ℕ) (U : Finset E) :
    Module.finrank K (jointSubspace (heldSpace K H n) U) =
      if (U ∩ H).Nonempty then n else 0 := by
  classical
  by_cases h : (U ∩ H).Nonempty
  · have hs : jointSubspace (heldSpace K H n) U = ⊤ := by
      simpa only [ite_eq_left h] using jointSubspace_heldSpace K H n U
    rw [hs]
    simp only [ite_eq_left h, finrank_top, Module.finrank_pi, Fintype.card_fin]
  · have hs : jointSubspace (heldSpace K H n) U = ⊥ := by
      simpa only [ite_eq_right h] using jointSubspace_heldSpace K H n U
    rw [hs]
    simp only [ite_eq_right h, finrank_bot]

@[simp] theorem inter_singleton_nonempty_iff (U : Finset E) (p : E) :
    (U ∩ {p}).Nonempty ↔ p ∈ U := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨hiU, hip⟩ := Finset.mem_inter.mp hi
    have heq : i = p := Finset.mem_singleton.mp hip
    simpa only [heq] using hiU
  · intro hp
    exact ⟨p, Finset.mem_inter.mpr ⟨hp, Finset.mem_singleton_self p⟩⟩

theorem private_joint_finrank (K : Type*) [Field K]
    (p : E) (U : Finset E) :
    Module.finrank K (jointSubspace (heldSpace K {p} 1) U) =
      if p ∈ U then 1 else 0 := by
  rw [heldSpace_joint_finrank]
  simp only [inter_singleton_nonempty_iff]

/-- One private scalar per participant contributes exactly coalition size. -/
theorem sum_private_joint_finrank (K : Type*) [Field K] [Fintype E]
    (U : Finset E) :
    (∑ p : E, Module.finrank K (jointSubspace (heldSpace K {p} 1) U)) =
      U.card := by
  simp [private_joint_finrank]

/-- The observation vector of the private scalar. -/
def privateKeyVector (K : Type*) [Field K] : Fin 1 → K :=
  fun _ => 1

theorem privateKeyVector_ne_zero (K : Type*) [Field K] :
    privateKeyVector K ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 1)
  simp [privateKeyVector] at h0

theorem privateKeyVector_mem_joint_iff (K : Type*) [Field K]
    (p : E) (U : Finset E) :
    privateKeyVector K ∈ jointSubspace (heldSpace K {p} 1) U ↔ p ∈ U := by
  rw [jointSubspace_heldSpace]
  simp only [inter_singleton_nonempty_iff]
  by_cases hp : p ∈ U
  · simp [hp]
  · simp [hp, privateKeyVector_ne_zero K]

/-- A private coordinate serves as a clause key precisely when the singleton
clause is present. An inactive private coordinate contributes zero to the secret. -/
theorem optionalPrivateKey_mem_joint_iff (K : Type*) [Field K]
    (active : Prop) [Decidable active] (p : E) (U : Finset E) :
    (if active then privateKeyVector K else 0) ∈
      jointSubspace (heldSpace K {p} 1) U ↔ (active → p ∈ U) := by
  by_cases ha : active
  · simpa only [ha, ite_true, true_implies] using
      privateKeyVector_mem_joint_iff K p U
  · simp [ha]

end BoundedArity
