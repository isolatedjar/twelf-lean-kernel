# Sourdough

This template project is part of Sourdough, a set of JavaScript templates that
were originally developed at Northeastern for their Software Engineering class
in spring of 2026.

## Base configuration

The functional content of this project is a minimal "transcript service" that
registers students by assigning them an ID and then lets course grades be
added and queried. Everything in the `./src` directory can be deleted to
create a true empty project.

The base project configuration follows a philosophy of "minimalism, mostly."
Project configuration should be minimal and have a bias towards implicit
defaults. Deviations from this principle should be justified and documented
(here or elsewhere).

Notable exceptions to this principle:

- `.gitignore` takes a kitchen-sink approach and should freely accept
  additions. (For example, if a student accidentally checks in a file that
  could have been ignored, it makes sense to add that file here.)

- The ESLint configuration is a maximalist attempt at keeping new TypeScript
  programmers on the rails in a complicated codebase, and also giving them a
  sense of working inside style conventions of a project that may differ from
  their own.

- If we can have all project variants using the _exact_ same `tsconfig.json`
  file or `eslint.config.mjs` file by adding a bit of cruft to the base
  configuration, that's a reasonable trade. Things are going to inevitably get
  copy-pasted, and so the fewer copies of configuration files there are, the
  better.

  This is why the `.vscode/settings.json` applies Prettier to html and css
  files even though that's not relevant to the base project, and why
  `eslint.config.mjs` includes React's Rules of Hooks despite most of the
  project variants not including any React code.

### NPM Scripts

This sets up a set of commands that CS4530 templates should consistently
support:

- `npm run check` runs TypeScript
- `npm run lint` runs ESLint, and `npm run lint:fix` runs eslint with the
  `--fix` option
- `npm run prettier` checks formatting, and `npm run prettier:fix` writes
  formatted files back to disk
- `npm run test` runs Vitest tests and reports coverage

When appropriate, projects should also have the following scripts:

- `npm run dev` starts a development server or watch process
- `npm run build` prepares the project for production-style deployment
- `npm start` runs the project in production mode

These are tested by github actions in `.github/workflows/main.yml`.

### ESLint

This base project has an opinionated ESLint configuration that relies on
[typed linting](https://typescript-eslint.io/getting-started/typed-linting).
The ESLint configuration makes some assumptions about project structure:

- Frontend code is code that lives in `./frontend` or `./client`, and
  optionally uses React and JSX. This code is subject to different linter
  rules.
- Test code lives in a `**/tests` directory OR has a `*.spec.ts(x)` or a
  `*.test.ts(x)` filename. Tests can use devDependencies, unlike other code.
- Config files all have `*.config.mjs` filenames (vite, vitest, playwright,
  and eslint all can follow this convention), so we're not using TypeScript to
  check our config files. Config files can also import devDependencies, like
  tests but unlike other code.
- Most everything should be registered as `error`. Warnings don't fail CI
  checks. Exceptions should have a documented reason. Notable exceptions:
  - `no-console` is `warn` because no-console regularly gets turned off by
    line or file specific rules: we want to discourage excessive `no-console`
    use but it is more like the admonition to not check in commented-out code:
    it's mostly a problem when done excessively and it's easy to check in
    visual inspection.
  - `prettier` is `warn` because red squigglies for `prettier` are especially
    distracting and we can check for prettier failures in CI separately.
  - We do not override the default setting of `warn` for
    `react-hooks/exhaustive-deps` in the default configuration. This rule
    makes the (horrible) suggestion to remove the dependency array, and people
    breaking their projects by blindly following that suggestion would be a
    bad outcome.

### TypeScript

TypeScript is configured with options that support
[type stripping](https://nodejs.org/api/typescript.html#type-stripping).
Beyond this, the TypeScript configuration enables
`noFallthroughCasesInSwitch`, `noImplicitOverride`, `noImplicitReturns`, and
`noUncheckedIndexedAccess`, which are linter-like properties that don't seem
to be well-supported by typed linting in ESLint.

[Matt Pocock's cheat sheet](https://www.totaltypescript.com/tsconfig-cheat-sheet)
is a reasonable source for more on minimal typescript configuration.

### Prettier

The `.prettierrc` file is intended to use some reasonable defaults. A
`.vscode/settings.json` file is added to encourage Visual Studio Code to treat
Prettier as the default formatter for javascript, typescript, json, css, and
html files even if a students' global configuration uses other defaults.

### LF Line Endings

The `.prettierrc`, `.gitattributes`, and `.vscode/settings.json` files
conspire to generally force projects to use `\n` file endings instead of
Windows-style `\r\n` line endings (LF instead of CRLF).

## Project Tree

The various Sourdough starters live in a single git repository as a series of
Git branches that build off of one another.

- [`base`](https://github.com/robsimmons/sourdough/tree/base), the base
  configuration
- [`express`](https://github.com/robsimmons/sourdough/tree/express), adds an
  Express server and API tests
- [`fullstack`](https://github.com/robsimmons/sourdough/tree/fullstack), adds
  a Vite frontend (+ Playwright end-to-end tests) for a simple client/server
  setup
- [`fullstack-react`](https://github.com/robsimmons/sourdough/tree/fullstack-react),
  makes the Vite frontend use React
- [`workspaces`](https://github.com/robsimmons/sourdough/tree/workspaces),
  uses NPM workspaces to mediate validation and types that can be productively
  shared between the frontend and backend

## Using Sourdough as a Starter

The `main` and `fullstack-react` branches should coincide, so you can use
GitHub to fork the full-stack React project by just forking this repository.

For other branches, or if you don't want to deal with the weirdness of being a
forked GitHub project, you'll want to follow a pattern like this, replacing
the three bits in square brackets as needed:

```sh
git init
git branch -M main
git remote add upstream git@github.com:robsimmons/sourdough.git
git remote add origin git@github.com:[MY_USERNAME]/[MY_PROJECT].git
git fetch upstream
git merge upstream/[THE_STARTER_YOU_WISH_TO_FORK]
git push -u origin main
```
