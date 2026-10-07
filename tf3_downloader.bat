@echo off
setlocal

rem Save current code page to restore it after exit.
for /f "tokens=2 delims=:" %%a in ('chcp') do set "OLD_CP=%%a"
set "OLD_CP=%OLD_CP: =%"

chcp 65001 >nul
set PYTHONIOENCODING=utf-8

set RC=0
set PY_CMD=

rem Find a working Python 3.11+.
python -c "import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)" >nul 2>nul
if not errorlevel 1 set PY_CMD=python

if "%PY_CMD%"=="" (
    py -3 -c "import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)" >nul 2>nul
    if not errorlevel 1 set PY_CMD=py -3
)

if "%PY_CMD%"=="" (
    echo Python 3.11+ not found. Install Python 3.11 or newer and add it to PATH.
    set RC=1
    goto :end
)

rem Check requests. Offer to install if missing.
%PY_CMD% -c "import requests" 2>nul
if not errorlevel 1 goto :run

echo requests is not installed.
set /p INSTALL=Install it now? (y/n): 
if /i "%INSTALL%"=="y" goto :install

echo Cannot continue without requests.
set RC=1
goto :end

:install
%PY_CMD% -m pip install requests
if errorlevel 1 (
    echo Installation failed. See pip output above.
    set RC=1
    goto :end
)

:run
%PY_CMD% "%~dp0tf3_downloader.py" %*
set RC=%errorlevel%

if %RC%==0 goto :ok
if %RC%==2 goto :warn
goto :err

:ok
echo Done.
goto :end

:warn
echo Finished with warnings. See summary above.
goto :end

:err
echo Finished with errors. See output above.

:end
echo.
pause
rem Restore original code page before exit.
if defined OLD_CP chcp %OLD_CP% >nul
endlocal & exit /b %RC%