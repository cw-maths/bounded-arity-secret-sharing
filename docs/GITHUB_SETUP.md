# Put this review repository on GitHub

The intended first destination is a **private** repository in a new
organization controlled by your existing personal GitHub account.
An organization gives the mathematical work its own name. You continue to
sign in with your existing personal login.

## 1. Create the organization

1. Sign in at [github.com](https://github.com/) with your personal account.
2. Click your profile picture, then **Settings**.
3. In the Access section, click **Organizations**, then **New organization**.
   You can also start at [your organizations settings](https://github.com/settings/organizations).
4. Choose **GitHub Free**. It supports private repositories and is sufficient
   for this initial review. Follow the prompts to choose an organization name
   and supply the required contact details.
5. If asked who the organization belongs to, choose the option indicating
   your personal account. Keep yourself as owner. You can skip inviting people
   until the repository is ready.

An illustrative name is `williamson-math`; availability has not been checked.
Use **New organization**, rather than converting your personal account into
an organization.

Official instructions: [create an organization](https://docs.github.com/en/organizations/collaborating-with-groups-in-organizations/creating-a-new-organization-from-scratch)
and [organization account features](https://docs.github.com/en/organizations/collaborating-with-groups-in-organizations/about-organizations).

## 2. Create an empty private repository

1. Open [New repository](https://github.com/new).
2. Set **Owner** to the new organization.
3. Set the name to `bounded-arity-secret-sharing` (suggested).
4. A suitable description is: `Lean formalization of a linear ceiling for
   bounded-arity information inequalities in secret sharing.`
5. Select **Private**.
6. Leave the options to add a README, .gitignore, and licence unselected:
   the prepared repository already has its own files and history.
7. Click **Create repository**. Keep the resulting page open and copy its
   HTTPS repository URL.

Official instructions: [create a repository](https://docs.github.com/en/repositories/creating-and-managing-repositories/creating-a-new-repository).

## 3. Open and check the prepared local repository

The delivered ZIP contains `bounded-arity-secret-sharing/`, including its
local Git history. It has no GitHub remote and no dependency/build caches.
Extract it into Documents. This creates a separate folder from the earlier
`bounded_arity_lean` milestone project.

In Terminal:

```sh
cd "$HOME/Documents/bounded-arity-secret-sharing"
git status
lake exe cache get
bash scripts/verify.sh --fresh-build
```

The verification command produces logs in `.verification/`. The Git worktree
should remain clean: dependencies, generated logs and build files are ignored.

## 4. Upload

Replace `YOUR-ORGANIZATION` in the following command with the organization
name you actually chose, or paste the HTTPS URL copied from GitHub:

```sh
git remote add origin https://github.com/YOUR-ORGANIZATION/bounded-arity-secret-sharing.git
git push -u origin main
```

The upload uses your local GitHub authentication. If your Mac is not yet
authenticated for Git, use the sign-in offered by VS Code/GitHub Desktop,
or GitHub CLI's `gh auth login` if the CLI is installed. An ordinary GitHub
account password is not the password for an HTTPS Git push. A failed sign-in
does not change the prepared repository; complete authentication and rerun
the push. Do not paste a token into the remote URL or into a chat message.

After the push, open the repository's **Actions** tab. Wait for the **Verify
Lean proofs** workflow to finish and inspect the job result. The code includes
the workflow, but it cannot have a GitHub run until uploaded. The local
verification report and the GitHub run are separate evidence.

Official guidance: [GitHub authentication](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/about-authentication-to-github)
and [GitHub CLI sign-in](https://cli.github.com/manual/gh_auth_login).

## 5. Invite the selected readers

In the repository, open **Settings → Collaborators & teams → Add people**.
Find the person by their actual GitHub username and grant **Read** access for
a discussion/review visit. Read access lets them clone the code, see the
checks, open issues and discuss the result. Grant Write only to someone who
will actively change the repository.

They can be outside collaborators on this repository; they do not need to
be organization owners or general organization members. A link by itself
does not grant access to a private repository. Each reader must accept the
invitation and sign in.

For an initial discussion, send them the repository link and the exact commit
you want them to review. The README states the result and its relationship to
earlier work; `docs/REVIEW_GUIDE.md` points to the formal definitions.

Official guidance: [manage repository access](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/managing-repository-settings/managing-teams-and-people-with-access-to-your-repository),
[outside collaborators](https://docs.github.com/en/organizations/managing-user-access-to-your-organizations-repositories/managing-outside-collaborators/adding-outside-collaborators-to-repositories-in-your-organization),
and [repository roles](https://docs.github.com/en/organizations/managing-user-access-to-your-organizations-repositories/managing-repository-roles/repository-roles-for-an-organization).

## Later wider release

Public visibility, a final reuse licence, final citation metadata, a tagged
archived release/DOI, and an expository preprint can be addressed when the mathematical
discussion and paper review are further along. None is required to give the
chosen readers access to this private review repository.
